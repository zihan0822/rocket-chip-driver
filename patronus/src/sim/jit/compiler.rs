use super::{runtime, JITResult, StateBufferView};
use crate::expr::{self, *};

use baa::{BitVecOps, BitVecValueRef};
use cranelift::codegen::ir::{self, condcodes::IntCC};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::Module;
use cranelift::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct JITCompiler {
    module: JITModule,
}

type CompiledEvalFnInternal = extern "C" fn(*const i64) -> i64;
pub(super) struct CompiledEvalFn {
    function: CompiledEvalFnInternal,
}

impl CompiledEvalFn {
    /// # Safety
    /// caller should guarantee the memory allocated for compiled code has not been reclaimed
    pub(super) unsafe fn call(&self, current_states: &[i64]) -> i64 {
        (self.function)(current_states.as_ptr())
    }
}

impl std::default::Default for JITCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl JITCompiler {
    pub(super) fn new() -> Self {
        let mut builder = JITBuilder::new(cranelift::module::default_libcall_names())
            .unwrap_or_else(|_| panic!("fail to launch jit instance"));
        runtime::load_runtime_lib(&mut builder);
        let module = JITModule::new(builder);
        Self { module }
    }

    pub(super) fn compile(
        &mut self,
        expr_ctx: &expr::Context,
        root_expr: ExprRef,
        input_state_buffer: &impl StateBufferView<i64>,
    ) -> JITResult<CompiledEvalFn> {
        let mut cranelift_ctx = self.module.make_context();
        cranelift_ctx.func.signature.params = vec![ir::AbiParam::new(types::I64)];
        cranelift_ctx.func.signature.returns = vec![ir::AbiParam::new(types::I64)];
        cranelift_ctx.func.signature.call_conv = isa::CallConv::SystemV;

        let runtime_lib =
            runtime::import_runtime_lib_to_func_scope(&mut self.module, &mut cranelift_ctx.func);
        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut cranelift_ctx.func, &mut fn_builder_ctx);

        let entry_block = fn_builder.create_block();
        fn_builder.append_block_params_for_function_params(entry_block);
        fn_builder.switch_to_block(entry_block);
        fn_builder.seal_block(entry_block);

        let codegen_ctx = CodeGenContext {
            fn_builder,
            runtime_lib,
            block_id: entry_block,
            expr_ctx,
            root_expr,
            input_state_buffer,
            heap_allocated: FxHashSet::default(),
            int: types::I64,
        };

        codegen_ctx.codegen();

        let function_id = self
            .module
            .declare_anonymous_function(&cranelift_ctx.func.signature)?;
        self.module
            .define_function(function_id, &mut cranelift_ctx)?;
        self.module.clear_context(&mut cranelift_ctx);
        self.module.finalize_definitions()?;

        let entry_address = self.module.get_finalized_function(function_id);

        // SAFETY: uphold by the unsafeness of CompiledEvalFn::call
        unsafe {
            Ok(CompiledEvalFn {
                function: std::mem::transmute::<*const u8, CompiledEvalFnInternal>(entry_address),
            })
        }
    }
}

struct CodeGenContext<'expr, 'ctx, 'engine> {
    fn_builder: FunctionBuilder<'ctx>,
    runtime_lib: runtime::RuntimeLib,
    block_id: Block,
    expr_ctx: &'expr expr::Context,
    root_expr: ExprRef,
    input_state_buffer: &'engine dyn StateBufferView<i64>,
    heap_allocated: FxHashSet<(Value, expr::Type)>,
    int: cranelift::prelude::Type,
}

#[derive(Debug)]
struct ExprNode {
    num_references: i64,
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen(mut self) {
        let ret = self.mock_interpret();
        self.fn_builder.ins().return_(&[ret]);
        self.fn_builder.finalize();
    }

    fn mock_interpret(&mut self) -> Value {
        let mut value_stack: Vec<Value> = Vec::new();
        let mut cached: FxHashMap<ExprRef, Value> = FxHashMap::default();

        let expr_nodes: FxHashMap<ExprRef, ExprNode> = self.expr_graph_topo();
        let mut todo: Vec<(ExprRef, bool)> = vec![(self.root_expr, false)];

        while let Some((e, args_available)) = todo.pop() {
            if let Some(&ret) = cached.get(&e) {
                value_stack.push(ret);
                continue;
            }
            let expr = &self.expr_ctx[e];
            if args_available {
                let num_children = expr.num_children();
                if let Expr::ArrayStore { array, .. } = expr {
                    if expr_nodes[array].num_references > 1 {
                        let cow = self.clone_array(
                            cached[array],
                            array.get_array_type(self.expr_ctx).unwrap(),
                        );
                        let stack_size = value_stack.len();
                        // first argument of `ArrayStore` operation is the src array
                        value_stack[stack_size - num_children..][0] = cow;
                    }
                }

                let ret = self.expr_codegen(e, &value_stack[value_stack.len() - num_children..]);
                value_stack.truncate(value_stack.len() - num_children);
                cached.insert(e, ret);
                value_stack.push(ret);
            } else {
                todo.push((e, true));
                let mut children = vec![];
                expr.collect_children(&mut children);
                todo.extend(children.into_iter().map(|child| (child, false)).rev());
            }
        }

        debug_assert_eq!(value_stack.len(), 1);
        // exclude potential allocation for the return value, which will be reclaimed in jit engine
        let heap_resources = self.heap_allocated.iter().copied().collect::<Vec<_>>();
        let ret =
            if let expr::Type::Array(tpe) = self.expr_ctx[self.root_expr].get_type(self.expr_ctx) {
                self.clone_array(value_stack[0], tpe)
            } else {
                value_stack[0]
            };
        self.reclaim_heap_resources(heap_resources);
        ret
    }

    /// Compute important expr graph statistics for better codegen
    ///
    /// Currently returns the number of upperstream references for each sub-expr.
    /// This allows us to determine whether we could steal heap allocated resources from sub-expr
    fn expr_graph_topo(&self) -> FxHashMap<ExprRef, ExprNode> {
        let mut expr_references: FxHashMap<ExprRef, ExprNode> = FxHashMap::default();
        let mut todo = vec![self.root_expr];
        while let Some(next) = todo.pop() {
            let visited = expr_references
                .entry(next)
                .and_modify(|node| node.num_references += 1)
                .or_insert(ExprNode { num_references: 1 })
                .num_references
                > 1;
            if !visited {
                self.expr_ctx[next].for_each_child(|&c| todo.push(c));
            }
        }
        expr_references
    }

    fn register_heap_allocation(&mut self, value: Value, tpe: expr::Type) {
        self.heap_allocated.insert((value, tpe));
    }

    fn reclaim_heap_resources(&mut self, items: impl IntoIterator<Item = (Value, expr::Type)>) {
        for (value, tpe) in items {
            if let expr::Type::Array(tpe) = tpe {
                self.dealloc_array(value, tpe);
            }
        }
    }
}

impl CodeGenContext<'_, '_, '_> {
    /// the meaning of the input state is polymorphic over bv/array
    fn load_input_state(&mut self, expr: ExprRef) -> Value {
        let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
        let input_buffer_address = self.fn_builder.block_params(self.block_id)[0];
        self.fn_builder.ins().load(
            self.int,
            // buffer is allocated by Rust, therefore trusted
            ir::MemFlags::trusted(),
            input_buffer_address,
            (param_offset * self.int.bytes()) as i32,
        )
    }

    fn dealloc_array(&mut self, array_to_dealloc: Value, tpe: ArrayType) {
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        self.fn_builder.ins().call(
            self.runtime_lib.dealloc_array,
            &[array_to_dealloc, index_width],
        );
    }

    fn clone_array(&mut self, from: Value, tpe: ArrayType) -> Value {
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let call = self
            .fn_builder
            .ins()
            .call(self.runtime_lib.clone_array, &[from, index_width]);
        let ret = self.fn_builder.inst_results(call)[0];
        self.register_heap_allocation(ret, expr::Type::Array(tpe));
        ret
    }

    fn alloc_const_array(&mut self, default_data: Value, tpe: ArrayType) -> Value {
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let call = self.fn_builder.ins().call(
            self.runtime_lib.alloc_const_array,
            &[index_width, default_data],
        );
        let ret = self.fn_builder.inst_results(call)[0];
        self.register_heap_allocation(ret, expr::Type::Array(tpe));
        ret
    }

    fn expr_codegen(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        match expr.get_type(self.expr_ctx) {
            expr::Type::BV(width) => assert!(width <= 64),
            expr::Type::Array(expr::ArrayType {
                index_width,
                data_width,
            }) => assert!(index_width <= 12 && data_width <= 64),
        }
        match &self.expr_ctx[expr] {
            Expr::ArraySymbol { .. } => {
                let src = self.load_input_state(expr);
                self.clone_array(src, expr.get_array_type(self.expr_ctx).unwrap())
            }
            Expr::BVIte { .. } | Expr::ArrayIte { .. } => {
                self.fn_builder.ins().select(args[0], args[1], args[2])
            }
            Expr::ArrayStore { .. } => {
                let (base, index, data) = (args[0], args[1], args[2]);
                let offset = self
                    .fn_builder
                    .ins()
                    .imul_imm(index, self.int.bytes() as i64);
                let address = self.fn_builder.ins().iadd(base, offset);
                self.fn_builder.ins().store(
                    // upheld by the unsafeness of CompiledEvalFn::call
                    ir::MemFlags::trusted(),
                    data,
                    address,
                    0,
                );
                base
            }
            Expr::BVArrayRead { .. } => {
                let (base, index) = (args[0], args[1]);
                let offset = self
                    .fn_builder
                    .ins()
                    .imul_imm(index, self.int.bytes() as i64);
                let address = self.fn_builder.ins().iadd(base, offset);
                self.fn_builder.ins().load(
                    self.int,
                    // upheld by the unsafeness of CompiledEvalFn::call
                    ir::MemFlags::trusted(),
                    address,
                    0,
                )
            }
            Expr::ArrayConstant { .. } => {
                self.alloc_const_array(args[0], expr.get_array_type(self.expr_ctx).unwrap())
            }
            _ => self.dispatch_bv_operation_codegen(expr, args),
        }
    }

    fn dispatch_bv_operation_codegen(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        let width = expr.get_bv_type(self.expr_ctx).unwrap();
        let vtable: Box<dyn BVCodeGenVTable> = match width {
            0..=64 => Box::new(BVWord(width)),
            _ => todo!(),
        };
        match self.expr_ctx[expr].clone() {
            Expr::BVSymbol { .. } => vtable.symbol(expr, self),
            Expr::BVLiteral(value) => vtable.literal(value.get(self.expr_ctx), self),
            // unary
            Expr::BVNot(..) => vtable.not(args[0], self),
            Expr::BVNegate(..) => vtable.negate(args[0], self),
            // no-op with current impl
            Expr::BVZeroExt { .. } => vtable.zero_ext(args[0], self),
            Expr::BVSignExt { by, .. } => vtable.sign_ext(args[0], by, self),
            Expr::BVSlice { hi, lo, .. } => vtable.slice(args[0], hi, lo, self),
            // binary
            Expr::BVAdd(..) => vtable.add(args[0], args[1], self),
            Expr::BVSub(..) => vtable.sub(args[0], args[1], self),
            Expr::BVMul(..) => vtable.mul(args[0], args[1], self),
            Expr::BVAnd(..) => vtable.and(args[0], args[1], self),
            Expr::BVOr(..) => vtable.or(args[0], args[1], self),
            Expr::BVXor(..) => vtable.xor(args[0], args[1], self),
            Expr::BVEqual(..) => vtable.equal(args[0], args[1], self),
            Expr::BVGreater(..) => vtable.gt(args[0], args[1], self),
            Expr::BVGreaterEqual(..) => vtable.ge(args[0], args[1], self),
            Expr::BVGreaterSigned(..) => vtable.gt_signed(args[0], args[1], self),
            Expr::BVGreaterEqualSigned(..) => vtable.ge_signed(args[0], args[1], self),
            Expr::BVShiftLeft(..) => vtable.shift_left(args[0], args[1], self),
            Expr::BVShiftRight(..) => vtable.shift_right(args[0], args[1], self),
            Expr::BVArithmeticShiftRight(..) => {
                vtable.arithmetic_shift_right(args[0], args[1], self)
            }
            Expr::BVConcat(_, lo, ..) => vtable.concat(
                args[0],
                args[1],
                lo.get_bv_type(self.expr_ctx).unwrap(),
                self,
            ),
            _ => todo!("{:?}", self.expr_ctx[expr]),
        }
    }
}

struct BVWord(WidthInt);
#[allow(dead_code)]
struct BVIndirect(WidthInt);

trait BVCodeGenVTable {
    fn symbol(&self, expr: ExprRef, ctx: &mut CodeGenContext) -> Value;
    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value;
    fn add(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn sub(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn mul(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn and(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn or(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn xor(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn not(&self, arg: Value, ctx: &mut CodeGenContext) -> Value;
    fn negate(&self, arg: Value, ctx: &mut CodeGenContext) -> Value;
    fn zero_ext(&self, arg: Value, ctx: &mut CodeGenContext) -> Value;
    fn sign_ext(&self, arg: Value, by: WidthInt, ctx: &mut CodeGenContext) -> Value;

    fn shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value;
    fn arithmetic_shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value;
    fn shift_left(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value;

    fn equal(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn gt(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn ge(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn gt_signed(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;
    fn ge_signed(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value;

    fn concat(&self, hi: Value, lo: Value, lo_width: WidthInt, ctx: &mut CodeGenContext) -> Value;
    fn slice(&self, value: Value, hi: WidthInt, lo: WidthInt, ctx: &mut CodeGenContext) -> Value;
}

impl BVWord {
    fn sign_extend_to_word(
        &self,
        value: Value,
        width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        let shifted = ctx.fn_builder.ins().ishl_imm(value, (64 - width) as i64);
        ctx.fn_builder.ins().sshr_imm(shifted, (64 - width) as i64)
    }

    fn overflow_guard(&self, value: Value, ctx: &mut CodeGenContext) -> Value {
        self.mask(value, self.0, ctx)
    }

    fn mask(&self, value: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width < 64 {
            ctx.fn_builder
                .ins()
                .band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
        } else {
            value
        }
    }

    fn cmp(&self, lhs: Value, rhs: Value, condcode: IntCC, ctx: &mut CodeGenContext) -> Value {
        let cmp = ctx.fn_builder.ins().icmp(condcode, lhs, rhs);
        ctx.fn_builder.ins().uextend(ctx.int, cmp)
    }
}

impl BVCodeGenVTable for BVWord {
    fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.load_input_state(arg), ctx)
    }

    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(
            ctx.fn_builder
                .ins()
                .iconst(ctx.int, value.to_i64().unwrap()),
            ctx,
        )
    }

    fn add(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().iadd(lhs, rhs), ctx)
    }
    fn sub(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().isub(lhs, rhs), ctx)
    }
    fn mul(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().imul(lhs, rhs), ctx)
    }

    fn and(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().band(lhs, rhs)
    }
    fn or(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bor(lhs, rhs)
    }
    fn xor(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bxor(lhs, rhs)
    }

    fn not(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().bnot(arg), ctx)
    }
    fn negate(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        let flipped = ctx.fn_builder.ins().bnot(arg);
        self.overflow_guard(ctx.fn_builder.ins().iadd_imm(flipped, 1), ctx)
    }
    fn zero_ext(&self, arg: Value, _ctx: &mut CodeGenContext) -> Value {
        arg
    }
    fn sign_ext(&self, arg: Value, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(self.sign_extend_to_word(arg, self.0 - by, ctx), ctx)
    }

    fn shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().ushr(arg0, arg1)
    }
    fn arithmetic_shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().sshr(arg0, arg1)
    }
    fn shift_left(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().ishl(arg0, arg1), ctx)
    }

    fn equal(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.cmp(lhs, rhs, IntCC::Equal, ctx)
    }
    fn gt(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.cmp(lhs, rhs, IntCC::UnsignedGreaterThan, ctx)
    }
    fn ge(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.cmp(lhs, rhs, IntCC::UnsignedGreaterThanOrEqual, ctx)
    }
    fn gt_signed(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.cmp(lhs, rhs, IntCC::SignedGreaterThan, ctx)
    }
    fn ge_signed(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.cmp(lhs, rhs, IntCC::SignedGreaterThanOrEqual, ctx)
    }

    fn concat(&self, hi: Value, lo: Value, lo_width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let hi = ctx.fn_builder.ins().ishl_imm(hi, lo_width as i64);
        ctx.fn_builder.ins().bor(hi, lo)
    }
    fn slice(&self, value: Value, hi: WidthInt, lo: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let shifted = ctx.fn_builder.ins().ushr_imm(value, lo as i64);
        self.mask(shifted, hi - lo + 1, ctx)
    }
}
