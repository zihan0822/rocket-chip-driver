// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::{JITResult, StateBufferView, THIN_BV_MAX_WIDTH, runtime};
use crate::expr::{self, *};
use crate::system::*;

use baa::{BitVecValue, BitVecValueRef};
use cranelift::codegen::ir;
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::Module;
use cranelift::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

/// we need a vec_box here because the address of those elements are implicitly
/// referenced by the compiled code. we need to make sure they are pinned on heap
#[expect(clippy::vec_box)]
pub(super) struct JITCompiler {
    module: JITModule,
    pub(super) bv_data: Vec<Box<BitVecValue>>,
    pub(super) array_data: Vec<Box<[i64]>>,
}

pub(super) struct EvalSingleExprWithUpdate(extern "C" fn(*const i64, *mut i64));
pub(super) struct EvalBatchedExprWithUpdate(extern "C" fn(*const i64, *mut i64));

impl EvalSingleExprWithUpdate {
    /// # Safety
    /// caller should guarantee the memory allocated for compiled code has not been reclaimed
    pub(super) unsafe fn call(&self, current_states: &[i64], ret_placeholder: *mut i64) {
        (self.0)(current_states.as_ptr(), ret_placeholder);
    }
}

impl EvalBatchedExprWithUpdate {
    /// # Safety
    /// caller should guarantee the memory allocated for compiled code has not been reclaimed
    pub(super) unsafe fn call(&self, current_states: &[i64], next_states: &mut [i64]) {
        (self.0)(current_states.as_ptr(), next_states.as_mut_ptr())
    }
}

impl Default for JITCompiler {
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
            array_data: vec![],
        }
    }

    pub(super) fn compile_transition_sys(
        &mut self,
        expr_ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &dyn StateBufferView<i64>,
        output_state_buffer: &dyn StateBufferView<i64>,
    ) -> JITResult<EvalBatchedExprWithUpdate> {
        let sig = Signature {
            params: vec![AbiParam::new(types::I64), AbiParam::new(types::I64)],
            returns: vec![],
            call_conv: isa::CallConv::SystemV,
        };

        let (next_expr_batch, states_expr): (Vec<_>, Vec<_>) = sys
            .states
            .iter()
            .filter_map(|state| state.next.map(|next| (next, state.symbol)))
            .unzip();

        self.enter_compile_ctx_with(
            sig,
            expr_ctx,
            next_expr_batch,
            input_state_buffer,
            |batch, mut codegen_ctx| {
                debug_assert_eq!(states_expr.len(), batch.len());
                for (expr, ret) in std::iter::zip(states_expr, batch) {
                    let param_offset = output_state_buffer.get_state_offset(expr) as u32;
                    let output_buffer_address =
                        codegen_ctx.fn_builder.block_params(codegen_ctx.block_id)[1];
                    let data_type = expr.get_type(expr_ctx);
                    let dst = if matches!(data_type, expr::Type::BV(width) if width <= THIN_BV_MAX_WIDTH) {
                        codegen_ctx.fn_builder.ins().iadd_imm(
                            output_buffer_address,
                            (param_offset * codegen_ctx.int.bytes()) as i64,
                        )
                    } else {
                        codegen_ctx.fn_builder.ins().load(
                            types::I64,
                            // buffer is allocated by Rust, therefore trusted
                            ir::MemFlags::trusted(),
                            output_buffer_address,
                            (param_offset * codegen_ctx.int.bytes()) as i32,
                        )
                    };
                    store_compiled_code_ret_at(dst, ret, data_type, &mut codegen_ctx);
                }
                codegen_ctx.fn_builder.ins().return_(&[]);
                codegen_ctx.fn_builder.finalize();
            },
        )
        .map(|address| unsafe {
            // SAFETY: upheld by the unsafeness of call method
            EvalBatchedExprWithUpdate(std::mem::transmute::<
                *const u8,
                extern "C" fn(*const i64, *mut i64),
            >(address))
        })
    }

    pub(super) fn compile_expr(
        &mut self,
        expr_ctx: &expr::Context,
        root_expr: ExprRef,
        input_state_buffer: &dyn StateBufferView<i64>,
    ) -> JITResult<EvalSingleExprWithUpdate> {
        let sig = Signature {
            params: vec![AbiParam::new(types::I64), AbiParam::new(types::I64)],
            returns: vec![],
            call_conv: isa::CallConv::SystemV,
        };

        self.enter_compile_ctx_with(
            sig,
            expr_ctx,
            vec![root_expr],
            input_state_buffer,
            |ret, mut codegen_ctx| {
                debug_assert_eq!(ret.len(), 1);
                let data_type = root_expr.get_type(expr_ctx);
                let dst = codegen_ctx.fn_builder.block_params(codegen_ctx.block_id)[1];
                store_compiled_code_ret_at(dst, ret[0], data_type, &mut codegen_ctx);
                codegen_ctx.fn_builder.ins().return_(&[]);
                codegen_ctx.fn_builder.finalize();
            },
        )
        .map(|address| unsafe {
            // SAFETY: upheld by the unsafeness of call method
            EvalSingleExprWithUpdate(std::mem::transmute::<
                *const u8,
                extern "C" fn(*const i64, *mut i64),
            >(address))
        })
    }

    fn enter_compile_ctx_with<F>(
        &mut self,
        sig: Signature,
        expr_ctx: &expr::Context,
        expr_batch: Vec<ExprRef>,
        input_state_buffer: &dyn StateBufferView<i64>,
        codegen_epilogue: F,
    ) -> JITResult<*const u8>
    where
        F: FnOnce(Vec<Value>, CodeGenContext),
    {
        let mut cranelift_ctx = self.module.make_context();
        cranelift_ctx.func.signature = sig;

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
            expr_batch,
            input_state_buffer,
            short_lived_heap_allocation: FxHashSet::default(),
            compiler: self,
            int: types::I64,
        };

        codegen_ctx.codegen(codegen_epilogue);

        let function_id = self
            .module
            .declare_anonymous_function(&cranelift_ctx.func.signature)?;
        self.module
            .define_function(function_id, &mut cranelift_ctx)?;
        self.module.clear_context(&mut cranelift_ctx);
        self.module.finalize_definitions()?;

        Ok(self.module.get_finalized_function(function_id))
    }
}

/// `dst` is a pointer to object with type aligned with `src`.
fn store_compiled_code_ret_at(
    dst: cranelift::prelude::Value,
    src: cranelift::prelude::Value,
    data_type: expr::Type,
    codegen_ctx: &mut CodeGenContext,
) {
    if matches!(data_type, expr::Type::BV(width) if width <= THIN_BV_MAX_WIDTH) {
        codegen_ctx
            .fn_builder
            .ins()
            .store(ir::MemFlags::trusted(), src, dst, 0);
        return;
    }
    let dst = TaggedValue {
        value: dst,
        data_type,
    };
    let src = TaggedValue {
        value: src,
        data_type,
    };
    match data_type {
        expr::Type::BV(..) => {
            codegen_ctx.copy_from_bv(dst, src);
        }
        expr::Type::Array(..) => codegen_ctx.copy_from_array(dst, src),
    }
}

pub(super) struct CodeGenContext<'expr, 'ctx, 'engine> {
    pub(super) fn_builder: FunctionBuilder<'ctx>,
    pub(super) runtime_lib: runtime::RuntimeLib,
    pub(super) expr_ctx: &'expr expr::Context,
    block_id: Block,
    expr_batch: Vec<ExprRef>,
    input_state_buffer: &'engine dyn StateBufferView<i64>,
    short_lived_heap_allocation: FxHashSet<TaggedValue>,
    pub(super) compiler: &'ctx mut JITCompiler,
    pub(super) int: cranelift::prelude::Type,
}

#[derive(Debug)]
struct ExprNode {
    num_references: i64,
}

#[derive(Debug, Clone, Copy)]
enum ExprNodeState {
    Root(bool),
    Intermediate(bool),
}

impl ExprNodeState {
    fn args_available(&self) -> bool {
        match self {
            Self::Root(available) => *available,
            Self::Intermediate(available) => *available,
        }
    }

    fn mark_as_args_available(self) -> Self {
        match self {
            Self::Root(..) => Self::Root(true),
            Self::Intermediate(..) => Self::Intermediate(true),
        }
    }
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen<F: FnOnce(Vec<Value>, Self)>(mut self, epilogue: F) {
        let ret = self.mock_interpret();
        epilogue(ret, self);
    }

    fn mock_interpret(&mut self) -> Vec<Value> {
        let mut value_stack: Vec<TaggedValue> = Vec::new();
        let mut cached: FxHashMap<ExprRef, TaggedValue> = FxHashMap::default();

        let expr_nodes: FxHashMap<ExprRef, ExprNode> = self.expr_graph_topo();
        let mut todo: Vec<(ExprRef, ExprNodeState)> = self
            .expr_batch
            .iter()
            .rev()
            .map(|&expr| (expr, ExprNodeState::Root(false)))
            .collect();

        while let Some((e, state)) = todo.pop() {
            if let Some(&ret) = cached.get(&e) {
                value_stack.push(ret);
                continue;
            }

            let expr = &self.expr_ctx[e];
            if state.args_available() {
                let num_children = expr.num_children();
                if let Expr::ArrayStore { array, .. } = expr {
                    if expr_nodes[array].num_references > 1 {
                        let cow = self.reserve_intermediate_array_cache(
                            expr.get_array_type(self.expr_ctx).unwrap(),
                        );
                        self.copy_from_array(cow, cached[array]);
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
                todo.push((e, state.mark_as_args_available()));
                let mut children = vec![];
                expr.collect_children(&mut children);
                todo.extend(
                    children
                        .into_iter()
                        .map(|child| (child, ExprNodeState::Intermediate(false)))
                        .rev(),
                );
                continue;
            }
        }

        // We have maintained the invariance that for every heap allocated value on the final value stack,
        // there is a long lived cache associated with it. Therefore, it is safe to reclaim all heap allocated object that has lifetime
        // tied to the eval function call here (before epilogue).
        self.reclaim_short_lived_heap_resources();
        value_stack.into_iter().map(|ret| *ret).collect()
    }

    /// Compute important expr graph statistics for better codegen
    ///
    /// Currently returns the number of upperstream references for each sub-expr.
    /// This allows us to determine whether we could steal heap allocated resources from sub-expr
    fn expr_graph_topo(&self) -> FxHashMap<ExprRef, ExprNode> {
        let mut expr_references: FxHashMap<ExprRef, ExprNode> = FxHashMap::default();
        let mut todo = self.expr_batch.clone();
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

    /// Heap allocations registered with this function are considered to be short lived as opposed to long lived cache.
    /// They have lifetime that ties to the eval function. Therefore, they will introduce heap transactions per eval function call.
    fn register_short_lived_heap_allocation(&mut self, value: TaggedValue) {
        self.short_lived_heap_allocation.insert(value);
    }

    fn reclaim_short_lived_heap_resources(&mut self) {
        for value in self.short_lived_heap_allocation.clone() {
            match value.data_type {
                expr::Type::Array(..) => self.dealloc_array(value),
                expr::Type::BV(width) => {
                    if width > THIN_BV_MAX_WIDTH {
                        self.dealloc_bv(value)
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
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
        matches!(self.data_type, expr::Type::BV(width) if width > THIN_BV_MAX_WIDTH)
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

    /// Reserves a long lived array cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    fn reserve_intermediate_array_cache(&mut self, tpe: ArrayType) -> TaggedValue {
        let cache = vec![0_i64; 1 << tpe.index_width].into_boxed_slice();
        let value = self
            .fn_builder
            .ins()
            .iconst(self.int, cache.as_ptr() as i64);
        self.compiler.array_data.push(cache);
        TaggedValue {
            value,
            data_type: expr::Type::Array(tpe),
        }
    }

    /// Reserves a long lived wide bit vector cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    pub(super) fn reserve_intermediate_bv_cache(&mut self, width: WidthInt) -> TaggedValue {
        assert!(width > THIN_BV_MAX_WIDTH);
        let cache = Box::new(BitVecValue::zero(width));
        let value = self
            .fn_builder
            .ins()
            .iconst(self.int, (&*cache) as *const BitVecValue as i64);
        self.compiler.bv_data.push(cache);
        TaggedValue {
            value,
            data_type: expr::Type::BV(width),
        }
    }

    fn copy_from_array(&mut self, dst: TaggedValue, src: TaggedValue) {
        let expr::Type::Array(tpe) = dst.data_type else {
            unreachable!()
        };
        assert_eq!(src.data_type, dst.data_type);
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let callee = if dst.data_type.get_array_data_width().unwrap() <= THIN_BV_MAX_WIDTH {
            self.runtime_lib.copy_from_array
        } else {
            self.runtime_lib.copy_from_array_of_wide_bv
        };
        self.fn_builder
            .ins()
            .call(callee, &[*dst, *src, index_width]);
    }

    fn dealloc_array(&mut self, array_to_dealloc: TaggedValue) {
        let expr::Type::Array(tpe) = array_to_dealloc.data_type else {
            unreachable!()
        };
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let callee =
            if array_to_dealloc.data_type.get_array_data_width().unwrap() <= THIN_BV_MAX_WIDTH {
                self.runtime_lib.dealloc_array
            } else {
                self.runtime_lib.dealloc_array_of_wide_bv
            };
        self.fn_builder
            .ins()
            .call(callee, &[*array_to_dealloc, index_width]);
    }

    #[expect(dead_code)]
    fn clone_array(&mut self, from: TaggedValue) -> TaggedValue {
        let expr::Type::Array(tpe) = from.data_type else {
            unreachable!()
        };
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let callee = if from.data_type.get_array_data_width().unwrap() <= THIN_BV_MAX_WIDTH {
            self.runtime_lib.clone_array
        } else {
            self.runtime_lib.clone_array_of_wide_bv
        };
        let call = self.fn_builder.ins().call(callee, &[*from, index_width]);
        let ret = TaggedValue {
            value: self.fn_builder.inst_results(call)[0],
            data_type: from.data_type,
        };
        self.register_short_lived_heap_allocation(ret);
        ret
    }

    fn alloc_array(&mut self, default_data: TaggedValue, tpe: ArrayType) -> TaggedValue {
        let index_width = self
            .fn_builder
            .ins()
            .iconst(self.int, tpe.index_width as i64);
        let callee = if tpe.data_width <= THIN_BV_MAX_WIDTH {
            self.runtime_lib.alloc_array
        } else {
            self.runtime_lib.alloc_array_of_wide_bv
        };
        let call = self
            .fn_builder
            .ins()
            .call(callee, &[index_width, *default_data]);
        let ret = TaggedValue {
            value: self.fn_builder.inst_results(call)[0],
            data_type: expr::Type::Array(tpe),
        };
        self.register_short_lived_heap_allocation(ret);
        ret
    }

    fn dealloc_bv(&mut self, bv_to_dealloc: TaggedValue) {
        self.fn_builder
            .ins()
            .call(self.runtime_lib.dealloc_bv, &[*bv_to_dealloc]);
    }

    #[expect(dead_code)]
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
        self.register_short_lived_heap_allocation(ret);
        ret
    }

    pub(super) fn copy_from_bv(&mut self, dst: TaggedValue, src: TaggedValue) {
        assert_eq!(src.data_type, dst.data_type);
        self.fn_builder
            .ins()
            .call(self.runtime_lib.copy_from_bv, &[*dst, *src]);
    }

    fn expr_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> TaggedValue {
        let value = match &self.expr_ctx[expr] {
            Expr::ArraySymbol { .. } => {
                let src = self.load_input_state(expr);
                let sym = self
                    .reserve_intermediate_array_cache(expr.get_array_type(self.expr_ctx).unwrap());
                self.copy_from_array(sym, src);
                return sym;
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
                let tpe = expr.get_array_type(self.expr_ctx).unwrap();
                // XXX: get rid of the extra alloc
                let array_const = self.alloc_array(args[0], tpe);
                let cache = self.reserve_intermediate_array_cache(tpe);
                self.copy_from_array(cache, array_const);
                return cache;
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
        let vtable: &dyn BVCodeGenVTable = match width {
            0..=64 => &super::bv_codegen::BVWord(width),
            _ => &super::bv_codegen::BVIndirect(width),
        };
        match self.expr_ctx[expr] {
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
