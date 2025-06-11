use super::{runtime, JITResult, StateBufferView};
use crate::expr::{self, *};

use baa::BitVecOps;
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

trait ExprRefExt {
    /// Returns the width of bitvector if the expr might cause overflow
    fn might_overflow(&self, ctx: &expr::Context) -> Option<WidthInt>;
}

impl ExprRefExt for ExprRef {
    fn might_overflow(&self, ctx: &expr::Context) -> Option<WidthInt> {
        if matches!(
            ctx[*self],
            Expr::BVAdd(..)
                | Expr::BVMul(..)
                | Expr::BVSub(..)
                | Expr::BVShiftLeft(..)
                | Expr::BVSignExt { .. }
                | Expr::BVNot(..)
                | Expr::BVNegate(..)
                | Expr::BVLiteral(..)
                | Expr::BVSymbol { .. }
        ) {
            self.get_type(ctx).get_bit_vector_width()
        } else {
            None
        }
    }
}

impl CodeGenContext<'_, '_, '_> {
    fn expr_codegen(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        let mut ret = self.expr_codegen_internal(expr, args);
        if let Some(width) = expr.might_overflow(self.expr_ctx) {
            ret = self.overflow_guard_codegen(ret, width);
        }
        ret
    }

    fn overflow_guard_codegen(&mut self, to_guard: Value, width: WidthInt) -> Value {
        assert!(width <= 64, "bv width greater than 64 is yet to implement");
        // case of 64 is handled by cranelift
        if width < 64 {
            self.fn_builder
                .ins()
                .band_imm(to_guard, ((u64::MAX) >> (64 - width)) as i64)
        } else {
            to_guard
        }
    }

    fn bv_sign_extend(&mut self, value: Value, width: WidthInt) -> Value {
        let shifted = self.fn_builder.ins().ishl_imm(value, (64 - width) as i64);
        self.fn_builder.ins().sshr_imm(shifted, (64 - width) as i64)
    }

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

    fn expr_codegen_internal(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        match expr.get_type(self.expr_ctx) {
            expr::Type::BV(width) => assert!(width <= 64),
            expr::Type::Array(expr::ArrayType {
                index_width,
                data_width,
            }) => assert!(index_width <= 12 && data_width <= 64),
        }
        match &self.expr_ctx[expr] {
            Expr::BVSymbol { .. } => self.load_input_state(expr),
            Expr::ArraySymbol { .. } => {
                let src = self.load_input_state(expr);
                self.clone_array(src, expr.get_array_type(self.expr_ctx).unwrap())
            }
            Expr::BVLiteral(value) => {
                let value = value.get(self.expr_ctx).to_i64().unwrap();
                self.fn_builder.ins().iconst(self.int, value)
            }
            // unary
            Expr::BVNot(..) => self.fn_builder.ins().bnot(args[0]),
            Expr::BVNegate(..) => {
                let flipped = self.fn_builder.ins().bnot(args[0]);
                self.fn_builder.ins().iadd_imm(flipped, 1)
            }
            // no-op with current impl
            Expr::BVZeroExt { .. } => args[0],
            Expr::BVSignExt { by, width, .. } => {
                assert!(width > by);
                self.bv_sign_extend(args[0], width - by)
            }
            Expr::BVSlice { hi, lo, .. } => {
                assert!(hi >= lo);
                let shifted = self.fn_builder.ins().ushr_imm(args[0], *lo as i64);
                self.fn_builder
                    .ins()
                    .band_imm(shifted, (u64::MAX >> (64 - (*hi - *lo + 1))) as i64)
            }
            // binary
            Expr::BVAdd(..) => self.fn_builder.ins().iadd(args[0], args[1]),
            Expr::BVSub(..) => self.fn_builder.ins().isub(args[0], args[1]),
            Expr::BVMul(..) => self.fn_builder.ins().imul(args[0], args[1]),
            Expr::BVAnd(..) => self.fn_builder.ins().band(args[0], args[1]),
            Expr::BVOr(..) => self.fn_builder.ins().bor(args[0], args[1]),
            Expr::BVXor(..) => self.fn_builder.ins().bxor(args[0], args[1]),
            Expr::BVEqual(..) => {
                let cmp = self.fn_builder.ins().icmp(IntCC::Equal, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreater(..) => {
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThan, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterSigned(.., width) => {
                let (arg0, arg1) = (
                    self.bv_sign_extend(args[0], *width),
                    self.bv_sign_extend(args[1], *width),
                );
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, arg0, arg1);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterEqual(..) => {
                let cmp =
                    self.fn_builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterEqualSigned(.., width) => {
                let (arg0, arg1) = (
                    self.bv_sign_extend(args[0], *width),
                    self.bv_sign_extend(args[1], *width),
                );
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, arg0, arg1);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVShiftLeft(..) => self.fn_builder.ins().ishl(args[0], args[1]),
            Expr::BVShiftRight(..) => self.fn_builder.ins().ushr(args[0], args[1]),
            Expr::BVArithmeticShiftRight(..) => self.fn_builder.ins().sshr(args[0], args[1]),
            Expr::BVIte { .. } | Expr::ArrayIte { .. } => {
                self.fn_builder.ins().select(args[0], args[1], args[2])
            }
            Expr::BVConcat(_, lo, ..) => {
                let expr::Type::BV(lo_width) = lo.get_type(self.expr_ctx) else {
                    unreachable!()
                };
                let hi = self.fn_builder.ins().ishl_imm(args[0], lo_width as i64);
                self.fn_builder.ins().bor(hi, args[1])
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
            _ => todo!("{:?}", self.expr_ctx[expr]),
        }
    }
}
