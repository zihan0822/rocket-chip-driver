// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::expr_graph::*;
use super::heap::*;
use super::{JITResult, StateBufferView, THIN_BV_MAX_WIDTH, runtime};
use crate::expr::{self, *};
use crate::system::*;

use baa::{BitVecValue, BitVecValueRef};
use cranelift::codegen::cursor::{Cursor, FuncCursor};
use cranelift::codegen::ir;
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::Module;
use cranelift::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct JITCompiler {
    module: JITModule,
    pub(super) sealed_heap_resources: Vec<ManagedHeapResource>,
    pub(super) active_heap_resource: ManagedHeapResource,
    pub(super) constant: ManagedHeapResource,
}

#[derive(Default)]
pub(super) struct ManagedHeapResource {
    pub(super) bv_data: HeapResourceCache<BitVecValue>,
    array_data: SlicedHeapResourceCache<i64>,
    array_with_wide_bv_data: SlicedHeapResourceCache<LeakedBitVecPtr>,
}

impl ManagedHeapResource {
    fn seal(&mut self) {
        self.bv_data.seal();
        self.array_data.seal();
        self.array_with_wide_bv_data.seal();
    }
}

#[repr(transparent)]
struct LeakedBitVecPtr(*mut BitVecValue);

impl LeakedBitVecPtr {
    fn new(data: BitVecValue) -> Self {
        Self(Box::into_raw(Box::new(data)))
    }
}

impl std::ops::Drop for LeakedBitVecPtr {
    fn drop(&mut self) {
        // SAFETY: `value` is leaked from Box in `Self::new`
        unsafe {
            let _ = Box::from_raw(self.0);
        }
    }
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
            sealed_heap_resources: vec![],
            active_heap_resource: Default::default(),
            constant: Default::default(),
        }
    }

    fn seal_active_heap_resource(&mut self) {
        self.active_heap_resource.seal();
        self.sealed_heap_resources
            .push(std::mem::take(&mut self.active_heap_resource));
    }

    fn last_pinned_heap_resource(&self) -> Option<&ManagedHeapResource> {
        self.sealed_heap_resources.last()
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
                    let dst_slot = codegen_ctx.fn_builder.ins().iadd_imm(
                        output_buffer_address,
                        (param_offset * codegen_ctx.int.bytes()) as i64,
                    );
                    try_swap_compiled_code_ret_with_slot(
                        dst_slot,
                        ret,
                        data_type,
                        &mut codegen_ctx,
                    );
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
                copy_compiled_code_ret_at(dst, ret[0], data_type, &mut codegen_ctx);
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
            long_live_cache_read_holes: vec![],
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
fn copy_compiled_code_ret_at(
    dst: Value,
    src: Value,
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
    let src = codegen_ctx.resource_ptr_at_slot(TaggedValue::tag(src, data_type));
    let dst = TaggedValue {
        value: dst,
        data_type,
    };
    match data_type {
        expr::Type::BV(..) => {
            codegen_ctx.copy_from_bv(dst, src);
        }
        expr::Type::Array(..) => codegen_ctx.copy_from_array(dst, src),
    }
}

fn try_swap_compiled_code_ret_with_slot(
    dst_slot: Value,
    src: Value,
    data_type: expr::Type,
    codegen_ctx: &mut CodeGenContext,
) {
    if matches!(data_type, expr::Type::BV(width) if width <= THIN_BV_MAX_WIDTH) {
        codegen_ctx
            .fn_builder
            .ins()
            .store(ir::MemFlags::trusted(), src, dst_slot, 0);
        return;
    }
    // `src` is interpreted as slot address of long lived heap resources
    swap_ptr_at_slot(codegen_ctx, dst_slot, src);
}

fn swap_ptr_at_slot(codegen_ctx: &mut CodeGenContext, slot_a: Value, slot_b: Value) {
    let ptr_a = codegen_ctx
        .fn_builder
        .ins()
        .load(codegen_ctx.int, MemFlags::trusted(), slot_a, 0);
    let ptr_b = codegen_ctx
        .fn_builder
        .ins()
        .load(codegen_ctx.int, MemFlags::trusted(), slot_b, 0);
    codegen_ctx
        .fn_builder
        .ins()
        .store(MemFlags::trusted(), ptr_b, slot_a, 0);
    codegen_ctx
        .fn_builder
        .ins()
        .store(MemFlags::trusted(), ptr_a, slot_b, 0);
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
    /// Points to the dummy instruction that will be replaced with a read instruction from long lived heap resources buffer.
    /// These replacement operations are done after codegen, when the number of long lived cache are determined.
    long_live_cache_read_holes: Vec<(Value, expr::Type)>,
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen<F: FnOnce(Vec<Value>, Self)>(mut self, epilogue: F) {
        let ret = self.mock_interpret();
        self.finalize_long_lived_heap_resources();
        epilogue(ret, self);
    }

    fn mock_interpret(&mut self) -> Vec<Value> {
        let mut evaluated: FxHashMap<ExprRef, TaggedValue> = FxHashMap::default();
        let bottom_up_expr_graph =
            BottomUpExprGraph::from_top_down_graph(self.expr_ctx, &self.expr_batch);

        // Track direct depedents of each array related expr node.
        // This allows us to determine whether we could steal heap allocated resources from operand expression.
        let mut array_references: FxHashMap<ExprRef, FxHashSet<ExprRef>> = bottom_up_expr_graph
            .node_dependents
            .iter()
            .filter_map(|(&expr, dependents)| {
                if expr.get_type(self.expr_ctx).is_array() {
                    Some((expr, FxHashSet::from_iter(dependents.iter().copied())))
                } else {
                    None
                }
            })
            .collect();

        let mut arguments = Vec::with_capacity(4);
        // Postpone `ArrayStore` as much as possible to reduce unnecessary clone of potentially huge array
        let walker = bottom_up_expr_graph.walker_with_sorted_fringe(|&a, _| {
            if matches!(self.expr_ctx[a], Expr::ArrayStore { .. }) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Less
            }
        });
        for e in walker {
            let expr = &self.expr_ctx[e];
            expr.for_each_child(|child| {
                if child.get_type(self.expr_ctx).is_array() {
                    array_references.get_mut(child).unwrap().remove(&e);
                }
                arguments.push(evaluated[child]);
            });
            if let Expr::ArrayStore { array, .. } = expr {
                if array_references[array].iter().any(|&other| {
                    if let Expr::ArrayIte { tru, fals, .. } = self.expr_ctx[other] {
                        if tru == e || fals == e {
                            return false;
                        }
                    }
                    !at_disjoint_branch(self.expr_ctx, &bottom_up_expr_graph, e, other)
                }) {
                    let cow_slot = self.reserve_intermediate_array_cache(
                        expr.get_array_type(self.expr_ctx).unwrap(),
                    );
                    let cow = self.resource_ptr_at_slot(cow_slot);
                    let src = self.resource_ptr_at_slot(evaluated[array]);
                    self.copy_from_array(cow, src);
                    // first argument of `ArrayStore` operation is the src array
                    arguments[0] = cow_slot;
                }
            }
            evaluated.insert(e, self.expr_codegen(e, &arguments));
            arguments.drain(..);
        }
        self.reclaim_short_lived_heap_resources();
        self.expr_batch.iter().map(|e| *evaluated[e]).collect()
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

    /// Register a hole that will be filled with pinned slot address of the resource after `mock_interpret` is done.
    ///
    /// We maintain the invariance that for every long lived heap resource there is a slot that contains the raw heap pointer
    /// to that during the entire lifetime of compiler. And that slot address won't change.
    fn phantom_register_long_lived_heap_resources(&mut self, tpe: expr::Type) -> TaggedValue {
        let phantom_src_addr = self.fn_builder.ins().iconst(self.int, 0);
        self.long_live_cache_read_holes
            .push((phantom_src_addr, tpe));
        TaggedValue::tag(phantom_src_addr, tpe)
    }

    /// Allocates all registered long-lived heap resources and pins them in a continuous buffer on heap.
    /// This extra level of indirection allows us to "swap" heap pointer with external pointer when necessary to reduce
    /// unnecessary heap allocation or data copy.
    fn finalize_long_lived_heap_resources(&mut self) {
        let mut bv_holes: Vec<Value> = vec![];
        let mut array_holes: Vec<Value> = vec![];
        let mut array_with_wide_bv_holes: Vec<Value> = vec![];
        for &(value, tpe) in &self.long_live_cache_read_holes {
            match tpe {
                expr::Type::BV(width) => {
                    debug_assert!(width > THIN_BV_MAX_WIDTH);
                    self.compiler
                        .active_heap_resource
                        .bv_data
                        .push(Box::new(BitVecValue::zero(width)));
                    bv_holes.push(value);
                }
                expr::Type::Array(ArrayType {
                    index_width,
                    data_width,
                }) => {
                    let index_width = index_width as usize;
                    if data_width <= THIN_BV_MAX_WIDTH {
                        let boxed_slice = vec![0i64; 1 << index_width].into_boxed_slice();
                        self.compiler
                            .active_heap_resource
                            .array_data
                            .push(boxed_slice);
                        array_holes.push(value);
                    } else {
                        let data: Vec<_> = std::iter::repeat_with(|| {
                            LeakedBitVecPtr::new(BitVecValue::zero(data_width))
                        })
                        .take(1 << index_width)
                        .collect();
                        self.compiler
                            .active_heap_resource
                            .array_with_wide_bv_data
                            .push(data.into_boxed_slice());
                        array_with_wide_bv_holes.push(value);
                    }
                }
            }
        }
        self.compiler.seal_active_heap_resource();
        let last_pinned = self.compiler.last_pinned_heap_resource().unwrap();
        for (holes, pinned_start_address) in [
            (bv_holes, last_pinned.bv_data.pinned_start_address()),
            (array_holes, last_pinned.array_data.pinned_start_address()),
            (
                array_with_wide_bv_holes,
                last_pinned.array_with_wide_bv_data.pinned_start_address(),
            ),
        ] {
            self.finalize_pinned_heap_resources(holes, pinned_start_address)
        }
    }

    fn finalize_pinned_heap_resources(
        &mut self,
        dummy_inst_values: impl IntoIterator<Item = Value>,
        pinned_start_address: *const i64,
    ) {
        for (offset, value) in dummy_inst_values.into_iter().enumerate() {
            self.fill_heap_cache_read_hole(
                value,
                (pinned_start_address as usize) + offset * size_of::<i64>(),
            )
        }
    }

    /// Removes the dummy instruction hole and fills it with the actual slot address.
    /// Since the slot address is guaranteed to be pinned during the lifetime of compiler, it's sound for us to directly
    /// hardcode the raw address with `iconst` inst.
    fn fill_heap_cache_read_hole(&mut self, dummy_inst_value: Value, src_addr: usize) {
        let ir::dfg::ValueDef::Result(dummy_inst, _) =
            self.fn_builder.func.dfg.value_def(dummy_inst_value)
        else {
            unreachable!()
        };
        let mut cursor = FuncCursor::new(self.fn_builder.func);
        cursor.goto_inst(dummy_inst);
        cursor.remove_inst();
        let read_src = cursor.ins().iconst(self.int, src_addr as i64);
        self.fn_builder
            .func
            .dfg
            .change_to_alias(dummy_inst_value, read_src);
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

    pub(super) fn expect_array_type(&self) -> ArrayType {
        match self.data_type {
            expr::Type::Array(tpe) => tpe,
            _ => panic!("expect array type"),
        }
    }

    pub(super) fn expect_bv_type(&self) -> WidthInt {
        match self.data_type {
            expr::Type::BV(tpe) => tpe,
            _ => panic!("expect bitvec type"),
        }
    }

    pub(super) fn tag(value: Value, data_type: expr::Type) -> Self {
        Self { value, data_type }
    }

    pub(super) fn tag_bv(value: Value, width: WidthInt) -> Self {
        Self::tag(value, expr::Type::BV(width))
    }

    pub(super) fn tag_array(value: Value, tpe: ArrayType) -> Self {
        Self::tag(value, expr::Type::Array(tpe))
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
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    /// Reserves a long lived array cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    fn reserve_intermediate_array_cache(&mut self, tpe: ArrayType) -> TaggedValue {
        self.phantom_register_long_lived_heap_resources(expr::Type::Array(tpe))
    }

    /// Reserves a long lived wide bit vector cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    pub(super) fn reserve_intermediate_bv_cache(&mut self, width: WidthInt) -> TaggedValue {
        assert!(width > THIN_BV_MAX_WIDTH);
        self.phantom_register_long_lived_heap_resources(expr::Type::BV(width))
    }

    pub(super) fn resource_ptr_at_slot(&mut self, slot_address: TaggedValue) -> TaggedValue {
        let ret = self
            .fn_builder
            .ins()
            .load(types::I64, ir::MemFlags::trusted(), *slot_address, 0);
        TaggedValue::tag(ret, slot_address.data_type)
    }

    fn copy_from_array(&mut self, dst: TaggedValue, src: TaggedValue) {
        let ArrayType {
            index_width,
            data_width,
        } = dst.expect_array_type();
        assert_eq!(src.data_type, dst.data_type);
        let index_width = self.fn_builder.ins().iconst(self.int, index_width as i64);
        let callee = if data_width <= THIN_BV_MAX_WIDTH {
            self.runtime_lib.copy_from_array
        } else {
            self.runtime_lib.copy_from_array_of_wide_bv
        };
        self.fn_builder
            .ins()
            .call(callee, &[*dst, *src, index_width]);
    }

    fn dealloc_array(&mut self, array_to_dealloc: TaggedValue) {
        let ArrayType {
            index_width,
            data_width,
        } = array_to_dealloc.expect_array_type();
        let index_width = self.fn_builder.ins().iconst(self.int, index_width as i64);
        let callee = if data_width <= THIN_BV_MAX_WIDTH {
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
        let ArrayType {
            index_width,
            data_width,
        } = from.expect_array_type();
        let index_width = self.fn_builder.ins().iconst(self.int, index_width as i64);
        let callee = if data_width <= THIN_BV_MAX_WIDTH {
            self.runtime_lib.clone_array
        } else {
            self.runtime_lib.clone_array_of_wide_bv
        };
        let call = self.fn_builder.ins().call(callee, &[*from, index_width]);
        let ret = TaggedValue::tag(self.fn_builder.inst_results(call)[0], from.data_type);
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
        let ret = TaggedValue::tag_array(self.fn_builder.inst_results(call)[0], tpe);
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
        let ret = TaggedValue::tag(self.fn_builder.inst_results(call)[0], src.data_type);
        self.register_short_lived_heap_allocation(ret);
        ret
    }

    pub(super) fn copy_from_bv(&mut self, dst: TaggedValue, src: TaggedValue) {
        assert_eq!(src.data_type, dst.data_type);
        self.fn_builder
            .ins()
            .call(self.runtime_lib.copy_from_bv, &[*dst, *src]);
    }

    fn reserve_cloned_intermediate_cache(&mut self, src: TaggedValue) -> TaggedValue {
        match src.data_type {
            expr::Type::Array(tpe) => {
                let slot = self.reserve_intermediate_array_cache(tpe);
                let dst = self.resource_ptr_at_slot(slot);
                self.copy_from_array(dst, src);
                slot
            }
            expr::Type::BV(tpe) => {
                let slot = self.reserve_intermediate_bv_cache(tpe);
                let dst = self.resource_ptr_at_slot(slot);
                self.copy_from_bv(dst, src);
                slot
            }
        }
    }

    fn expr_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> TaggedValue {
        let value = match &self.expr_ctx[expr] {
            Expr::ArraySymbol { .. } => {
                let src = self.load_input_state(expr);
                return self.reserve_cloned_intermediate_cache(src);
            }
            Expr::BVIte { .. } | Expr::ArrayIte { .. } => {
                self.fn_builder.ins().select(*args[0], *args[1], *args[2])
            }
            Expr::ArrayStore { .. } => {
                let array_type = args[0].expect_array_type();
                let data_width = array_type.data_width;
                let (slot, index, data) = (args[0], *args[1], args[2]);
                let base = self.resource_ptr_at_slot(slot);
                let offset = self
                    .fn_builder
                    .ins()
                    .imul_imm(index, self.int.bytes() as i64);
                let address = self.fn_builder.ins().iadd(*base, offset);
                if data_width > THIN_BV_MAX_WIDTH {
                    let dst_bv = self.fn_builder.ins().load(
                        self.int,
                        // upheld by the unsafeness of CompiledEvalFn::call
                        ir::MemFlags::trusted(),
                        address,
                        0,
                    );
                    let data = self.resource_ptr_at_slot(data);
                    self.copy_from_bv(TaggedValue::tag_bv(dst_bv, data_width), data);
                } else {
                    self.fn_builder.ins().store(
                        // upheld by the unsafeness of CompiledEvalFn::call
                        ir::MemFlags::trusted(),
                        *data,
                        address,
                        0,
                    );
                }
                return slot;
            }
            Expr::BVArrayRead { .. } => {
                let data_width = args[0].expect_array_type().data_width;
                let (slot, index) = (args[0], *args[1]);
                let base = self.resource_ptr_at_slot(slot);
                let offset = self
                    .fn_builder
                    .ins()
                    .imul_imm(index, self.int.bytes() as i64);
                let address = self.fn_builder.ins().iadd(*base, offset);
                let element = self.fn_builder.ins().load(
                    self.int,
                    // upheld by the unsafeness of CompiledEvalFn::call
                    ir::MemFlags::trusted(),
                    address,
                    0,
                );
                if data_width > THIN_BV_MAX_WIDTH {
                    // maintains the invariance that wide bv never moves out of its container array
                    return self.reserve_cloned_intermediate_cache(TaggedValue::tag_bv(
                        element, data_width,
                    ));
                }
                element
            }
            Expr::ArrayConstant { .. } => {
                let tpe = expr.get_array_type(self.expr_ctx).unwrap();
                // XXX: get rid of the extra alloc
                let array_const = self.alloc_array(args[0], tpe);
                return self.reserve_cloned_intermediate_cache(array_const);
            }
            _ => self.dispatch_bv_operation_codegen(expr, args),
        };
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    fn dispatch_bv_operation_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> Value {
        let width = expr.get_bv_type(self.expr_ctx).unwrap();
        let vtable: &dyn BVCodeGenVTable = match width {
            0..=64 => &super::bv_codegen::BVWord(width),
            _ => &super::bv_codegen::BVIndirect(width),
        };
        let args: Vec<_> = args
            .iter()
            .map(|&arg| {
                if arg.requires_bv_delegation() {
                    self.resource_ptr_at_slot(arg)
                } else {
                    arg
                }
            })
            .collect();

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
