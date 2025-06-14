use super::{runtime, JITResult, StateBufferView};
use crate::expr::{self, *};

use baa::{BitVecValue, BitVecValueRef};
use cranelift::codegen::ir;
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::Module;
use cranelift::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct JITCompiler {
    module: JITModule,
    /// we need a vec_box instead of vec of `BitVecValue` here because
    /// the address of those elements are implicitly referenced by the compiled code.
    /// we need to make sure they are pinned on heap
    #[allow(clippy::vec_box)]
    bv_data: Vec<Box<BitVecValue>>,
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
        Self {
            module,
            bv_data: vec![],
        }
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
            bv_data: &mut self.bv_data,
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

pub(super) struct CodeGenContext<'expr, 'ctx, 'engine> {
    pub(super) fn_builder: FunctionBuilder<'ctx>,
    pub(super) runtime_lib: runtime::RuntimeLib,
    pub(super) expr_ctx: &'expr expr::Context,
    block_id: Block,
    root_expr: ExprRef,
    input_state_buffer: &'engine dyn StateBufferView<i64>,
    heap_allocated: FxHashSet<TaggedValue>,
    /// See JITCompiler bv_data field
    #[allow(clippy::vec_box)]
    pub(super) bv_data: &'ctx mut Vec<Box<BitVecValue>>,
    pub(super) int: cranelift::prelude::Type,
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
        let mut value_stack: Vec<TaggedValue> = Vec::new();
        let mut cached: FxHashMap<ExprRef, TaggedValue> = FxHashMap::default();

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
                        let cow = self.clone_array(cached[array]);
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
        let ret = match self.root_expr.get_type(self.expr_ctx) {
            expr::Type::Array(..) => self.clone_array(value_stack[0]),
            expr::Type::BV(width) if width > 64 => self.clone_bv(value_stack[0]),
            _ => value_stack[0],
        };
        self.reclaim_heap_resources(heap_resources);
        *ret
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

    pub(super) fn register_heap_allocation(&mut self, value: TaggedValue) {
        self.heap_allocated.insert(value);
    }

    fn reclaim_heap_resources(&mut self, items: impl IntoIterator<Item = TaggedValue>) {
        for value in items {
            match value.data_type {
                expr::Type::Array(..) => self.dealloc_array(value),
                expr::Type::BV(width) => {
                    if width > 64 {
                        self.dealloc_bv(value)
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct TaggedValue {
    pub(super) value: Value,
    pub(super) data_type: expr::Type,
}

impl std::ops::Deref for TaggedValue {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl TaggedValue {
    pub(super) fn requires_bv_delegation(&self) -> bool {
        matches!(self.data_type, expr::Type::BV(width) if width > 64)
    }
}

impl CodeGenContext<'_, '_, '_> {
    /// the meaning of the input state is polymorphic over bv/array
    pub(super) fn load_input_state(&mut self, expr: ExprRef) -> TaggedValue {
        let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
        let input_buffer_address = self.fn_builder.block_params(self.block_id)[0];
        let value = self.fn_builder.ins().load(
            self.int,
            // buffer is allocated by Rust, therefore trusted
            ir::MemFlags::trusted(),
            input_buffer_address,
            (param_offset * self.int.bytes()) as i32,
        );
        TaggedValue {
            value,
            data_type: expr.get_type(self.expr_ctx),
        }
    }

    fn dealloc_array(&mut self, array_to_dealloc: TaggedValue) {
        let expr::Type::Array(tpe) = array_to_dealloc.data_type else {
            unreachable!()
        };
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        self.fn_builder.ins().call(
            self.runtime_lib.dealloc_array,
            &[*array_to_dealloc, index_width],
        );
    }

    fn clone_array(&mut self, from: TaggedValue) -> TaggedValue {
        let expr::Type::Array(tpe) = from.data_type else {
            unreachable!()
        };
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let call = self
            .fn_builder
            .ins()
            .call(self.runtime_lib.clone_array, &[*from, index_width]);
        let ret = TaggedValue {
            value: self.fn_builder.inst_results(call)[0],
            data_type: from.data_type,
        };
        self.register_heap_allocation(ret);
        ret
    }

    fn alloc_const_array(&mut self, default_data: TaggedValue, tpe: ArrayType) -> TaggedValue {
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let call = self.fn_builder.ins().call(
            self.runtime_lib.alloc_const_array,
            &[index_width, *default_data],
        );
        let ret = TaggedValue {
            value: self.fn_builder.inst_results(call)[0],
            data_type: expr::Type::Array(tpe),
        };
        self.register_heap_allocation(ret);
        ret
    }

    fn dealloc_bv(&mut self, bv_to_dealloc: TaggedValue) {
        self.fn_builder
            .ins()
            .call(self.runtime_lib.dealloc_bv, &[*bv_to_dealloc]);
    }

    pub(super) fn clone_bv(&mut self, src: TaggedValue) -> TaggedValue {
        assert!(src.requires_bv_delegation());
        let call = self
            .fn_builder
            .ins()
            .call(self.runtime_lib.clone_bv, &[*src]);
        let ret = TaggedValue {
            value: self.fn_builder.inst_results(call)[0],
            data_type: src.data_type,
        };
        self.register_heap_allocation(ret);
        ret
    }

    fn expr_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> TaggedValue {
        if let expr::Type::Array(expr::ArrayType {
            index_width,
            data_width,
        }) = expr.get_type(self.expr_ctx)
        {
            assert!(index_width <= 12 && data_width <= 64);
        }
        let value = match &self.expr_ctx[expr] {
            Expr::ArraySymbol { .. } => {
                let src = self.load_input_state(expr);
                return self.clone_array(src);
            }
            Expr::BVIte { .. } | Expr::ArrayIte { .. } => {
                self.fn_builder.ins().select(*args[0], *args[1], *args[2])
            }
            Expr::ArrayStore { .. } => {
                let (base, index, data) = (*args[0], *args[1], *args[2]);
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
                let (base, index) = (*args[0], *args[1]);
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
                return self
                    .alloc_const_array(args[0], expr.get_array_type(self.expr_ctx).unwrap());
            }
            _ => self.dispatch_bv_operation_codegen(expr, args),
        };
        TaggedValue {
            value,
            data_type: expr.get_type(self.expr_ctx),
        }
    }

    fn dispatch_bv_operation_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> Value {
        let width = expr.get_bv_type(self.expr_ctx).unwrap();
        let vtable: Box<dyn BVCodeGenVTable> = match width {
            0..=64 => Box::new(super::bv_codegen::BVWord(width)),
            _ => Box::new(super::bv_codegen::BVIndirect(width)),
        };
        match self.expr_ctx[expr].clone() {
            Expr::BVSymbol { .. } => vtable.symbol(expr, self),
            Expr::BVLiteral(value) => vtable.literal(value.get(self.expr_ctx), self),
            // unary
            Expr::BVNot(..) => vtable.not(args[0], self),
            Expr::BVNegate(..) => vtable.negate(args[0], self),
            // no-op with current impl
            Expr::BVZeroExt { by, .. } => vtable.zero_extend(args[0], by, self),
            Expr::BVSignExt { by, .. } => vtable.sign_extend(args[0], by, self),
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
            Expr::BVConcat(..) => vtable.concat(args[0], args[1], self),
            _ => todo!("{:?}", self.expr_ctx[expr]),
        }
    }
}

pub(super) trait BVCodeGenVTable {
    fn symbol(&self, expr: ExprRef, ctx: &mut CodeGenContext) -> Value;
    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value;
    fn add(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn sub(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn mul(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn and(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn or(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn xor(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn not(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn negate(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn zero_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value;
    fn sign_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value;

    fn shift_right(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn arithmetic_shift_right(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value;
    fn shift_left(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value;

    fn equal(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn gt(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn ge(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn gt_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn ge_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;

    fn concat(&self, hi: TaggedValue, lo: TaggedValue, ctx: &mut CodeGenContext) -> Value;
    fn slice(
        &self,
        value: TaggedValue,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value;
}
