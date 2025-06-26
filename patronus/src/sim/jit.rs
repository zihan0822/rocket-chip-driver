// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
mod bv_codegen;
mod compiler;
mod runtime;

use super::*;
use crate::expr::{self, *};
use crate::system::*;
use baa::*;
use compiler::*;
use cranelift::module::ModuleError;
use fixedbitset::FixedBitSet;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;

type JITResult<T> = Result<T, JITError>;

#[derive(Debug)]
pub enum JITError {
    /// box here due to large size of ModuleError
    CompileError(Box<ModuleError>),
}

impl From<ModuleError> for JITError {
    fn from(value: ModuleError) -> Self {
        Self::CompileError(Box::new(value))
    }
}

trait StateBufferView<T> {
    fn get_state_offset(&self, expr: ExprRef) -> usize;
    fn get_state_ref(&self, expr: ExprRef) -> &T;
    fn as_slice(&self) -> &[T];
}

trait StateBufferViewMut<T>: StateBufferView<T> {
    fn get_state_mut(&mut self, expr: ExprRef) -> &mut T;
    fn as_mut_slice(&mut self) -> &mut [T];
}

struct StateBuffer<'engine, B> {
    buffer: B,
    states_to_offset: &'engine FxHashMap<ExprRef, usize>,
    ctx: &'engine expr::Context,
}

impl<B> StateBufferView<i64> for StateBuffer<'_, B>
where
    B: std::borrow::Borrow<[i64]>,
{
    fn get_state_offset(&self, expr: ExprRef) -> usize {
        self.states_to_offset[&expr]
    }

    fn get_state_ref(&self, expr: ExprRef) -> &i64 {
        let offset = self.get_state_offset(expr);
        &self.buffer.borrow()[offset]
    }
    fn as_slice(&self) -> &[i64] {
        self.buffer.borrow()
    }
}

impl<B> StateBufferViewMut<i64> for StateBuffer<'_, B>
where
    B: std::borrow::BorrowMut<[i64]>,
{
    fn get_state_mut(&mut self, expr: ExprRef) -> &mut i64 {
        let offset = self.get_state_offset(expr);
        &mut self.buffer.borrow_mut()[offset]
    }
    fn as_mut_slice(&mut self) -> &mut [i64] {
        self.buffer.borrow_mut()
    }
}

const CURRENT_STATE_INDEX: usize = 0;
const NEXT_STATE_INDEX: usize = 1;
const BATCHED_UPDATE_THRESHOLD: f64 = 0.6;

enum DirtyUpdatePolicy {
    Sparse,
    Batched,
}
struct DirtyStateRegistry {
    states: FixedBitSet,
    num_total_states: f64,
}

impl DirtyStateRegistry {
    fn new(init_states: FixedBitSet, num_total_states: usize) -> Self {
        Self {
            states: init_states,
            num_total_states: num_total_states as f64,
        }
    }

    #[inline]
    fn register(&mut self, dirty_states: &FixedBitSet) {
        self.states.union_with(dirty_states);
    }

    #[inline]
    fn clear_and_track(&mut self, dirty_states: FixedBitSet) {
        self.states = dirty_states;
    }

    fn select_update_policy(&self) -> DirtyUpdatePolicy {
        let dirty_percentage = (self.states.count_ones(..) as f64) / self.num_total_states;
        if dirty_percentage >= BATCHED_UPDATE_THRESHOLD {
            DirtyUpdatePolicy::Batched
        } else {
            DirtyUpdatePolicy::Sparse
        }
    }

    #[inline]
    fn dirty_percentage(&self) -> f64 {
        (self.states.count_ones(..) as f64) / self.num_total_states
    }
}

pub struct JITEngine<'expr> {
    buffers: [Box<[i64]>; 2],
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    /// non-init bv states, resources allocated for those states will be reclaimed during every step
    mortal_states: Vec<ExprRef>,
    /// init and array states, resources allocated for those states will only be reclaimed when dropping the JITEngine
    immortal_states: Vec<ExprRef>,
    /// for each leaf state, tracks all root state expr that transitively depends on it
    upstream_dependencies: FxHashMap<ExprRef, FixedBitSet>,
    /// maintains set of states that need to be recomputed at next step
    dirty_registry: DirtyStateRegistry,
    /// states corresponding to the first `sys.states.len()` expr in the state buffer
    /// types are cached for better perf
    mutable_slot_states: Vec<(State, expr::Type)>,
    states_to_offset: FxHashMap<ExprRef, usize>,
    step_count: u64,
}

#[derive(Default)]
struct JITBackend {
    compiler: JITCompiler,
    compiled_transition_sys: Option<EvalBatchedExprWithUpdate>,
    compiled_expr_eval: FxHashMap<ExprRef, EvalSingleExpr>,
}

impl JITBackend {
    fn eval_expr(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &impl StateBufferView<i64>,
    ) -> i64 {
        let eval_fn = self.compiled_expr_eval.entry(expr).or_insert_with(|| {
            self.compiler
                .compile_expr(ctx, expr, input_state_buffer)
                .unwrap_or_else(|err| panic!("fail to compile: `{:?}` due to {:?}", ctx[expr], err))
        });

        // SAFETY: jit compiler has not been dropped
        unsafe { eval_fn.call(input_state_buffer.as_slice()) }
    }

    fn step_transition_sys(
        &mut self,
        ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &impl StateBufferView<i64>,
        output_state_buffer: &mut impl StateBufferViewMut<i64>,
    ) {
        let eval_fn = self.compiled_transition_sys.get_or_insert_with(|| {
            self.compiler
                .compile_transition_sys(ctx, sys, input_state_buffer, &*output_state_buffer)
                .unwrap_or_else(|err| {
                    panic!("fail to compile transition step function, due to {:?}", err)
                })
        });

        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_mut_slice(),
            )
        }
    }
}

macro_rules! current_state_buffer {
    ($engine: ident) => {
        StateBuffer {
            buffer: &*$engine.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &$engine.states_to_offset,
            ctx: $engine.ctx,
        }
    };
}

macro_rules! current_state_buffer_mut {
    ($engine: ident) => {
        StateBuffer {
            buffer: &mut *$engine.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &$engine.states_to_offset,
            ctx: $engine.ctx,
        }
    };
}

macro_rules! next_state_buffer {
    ($engine: ident) => {
        StateBuffer {
            buffer: &mut *$engine.buffers[NEXT_STATE_INDEX],
            states_to_offset: &$engine.states_to_offset,
            ctx: $engine.ctx,
        }
    };
}

macro_rules! next_state_buffer_mut {
    ($engine: ident) => {
        StateBuffer {
            buffer: &mut *$engine.buffers[NEXT_STATE_INDEX],
            states_to_offset: &$engine.states_to_offset,
            ctx: $engine.ctx,
        }
    };
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let mut states_to_offset: FxHashMap<ExprRef, usize> = FxHashMap::default();
        let mut mutable_slot_states: Vec<(State, expr::Type)> = vec![];
        for state in &sys.states {
            mutable_slot_states.push((state.clone(), state.symbol.get_type(ctx)));
            let offset = states_to_offset.len();
            states_to_offset.entry(state.symbol).or_insert(offset);
        }
        for &input in &sys.inputs {
            let offset = states_to_offset.len();
            states_to_offset.entry(input).or_insert(offset);
        }

        let mortal_states = sys
            .states
            .iter()
            .filter_map(|state| {
                if let expr::Type::BV(..) = state.symbol.get_type(ctx) {
                    Some(state.symbol)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let immortal_states = sys
            .states
            .iter()
            .filter_map(|state| {
                if let expr::Type::Array(..) = state.symbol.get_type(ctx) {
                    Some(state.symbol)
                } else {
                    None
                }
            })
            .chain(sys.inputs.iter().copied())
            .collect::<Vec<_>>();

        let buffers: [Box<[i64]>; 2] =
            std::array::from_fn(|_| vec![0_i64; states_to_offset.len()].into_boxed_slice());

        let mut init_states = FixedBitSet::with_capacity(mutable_slot_states.len());
        init_states.insert_range(..);
        let dirty_registry = DirtyStateRegistry::new(init_states, mutable_slot_states.len());

        let mut engine = Self {
            backend: RefCell::default(),
            mortal_states,
            immortal_states,
            mutable_slot_states,
            buffers,
            ctx,
            sys,
            states_to_offset,
            upstream_dependencies: FxHashMap::default(),
            dirty_registry,
            step_count: 0,
        };
        engine.bootstrap_state_buffers();
        engine.find_leaf_states_upstream_dep();
        engine
    }

    fn find_leaf_states_upstream_dep(&mut self) {
        let mut todo = Vec::from_iter(
            self.sys
                .states
                .iter()
                .filter_map(|state| state.next.map(|next| (state.clone(), next))),
        );
        while let Some((root, next)) = todo.pop() {
            let expr = &self.ctx[next];
            if expr.num_children() == 0 && expr.is_symbol() {
                let dependents = self
                    .upstream_dependencies
                    .entry(next)
                    .or_insert_with(|| FixedBitSet::with_capacity(self.mutable_slot_states.len()));
                let offset_in_state_buffer = self.states_to_offset[&root.symbol];
                if offset_in_state_buffer < self.mutable_slot_states.len() {
                    dependents.insert(offset_in_state_buffer);
                }
            } else {
                expr.for_each_child(|&child| todo.push((root.clone(), child)));
            }
        }
    }

    /// Maintains the invariance that all heap allocated states in the current buffer
    /// and all heap allocated init(immortal) states in the next buffer point to a valid object
    fn bootstrap_state_buffers(&mut self) {
        for &state in self.mortal_states.iter().chain(&self.immortal_states) {
            match state.get_type(self.ctx) {
                expr::Type::Array(expr::ArrayType {
                    index_width,
                    data_width,
                }) => {
                    assert!(
                        data_width <= 64,
                        "only support bv with width less than equal to 64, but got `{}`",
                        data_width
                    );
                    assert!(
                    index_width <= 12,
                    "currently no sparse array support, size of the dense array should be less than or equal to 2^12, but got `{}`", 
                    index_width
                );
                    *current_state_buffer_mut!(self).get_state_mut(state) =
                        runtime::__alloc_const_array(index_width, 0) as i64;
                }
                expr::Type::BV(width) => {
                    if width > 64 {
                        *current_state_buffer_mut!(self).get_state_mut(state) =
                            runtime::__alloc_bv(width) as i64;
                    }
                }
            }
        }

        for &state in self.mortal_states.iter().chain(self.immortal_states.iter()) {
            match state.get_type(self.ctx) {
                expr::Type::Array(ArrayType { index_width, .. }) => {
                    *next_state_buffer_mut!(self).get_state_mut(state) =
                        runtime::__alloc_const_array(index_width, 0) as i64;
                }
                expr::Type::BV(width) => {
                    if width > 64 {
                        *next_state_buffer_mut!(self).get_state_mut(state) =
                            runtime::__alloc_bv(width) as i64;
                    }
                }
            }
        }
    }

    fn eval_expr(&self, expr: ExprRef) -> i64 {
        self.backend
            .borrow_mut()
            .eval_expr(expr, self.ctx, &current_state_buffer!(self))
    }

    fn step_transition_sys(&mut self) {
        let (current, next) = self.buffers.split_at_mut(NEXT_STATE_INDEX);
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
            &StateBuffer {
                buffer: &*current[0],
                states_to_offset: &self.states_to_offset,
                ctx: self.ctx,
            },
            &mut StateBuffer {
                buffer: &mut *next[0],
                states_to_offset: &self.states_to_offset,
                ctx: self.ctx,
            },
        );
    }

    /// Maintains the invariance that before each step, the heap resources allocated
    /// in the output buffer are reclaimed
    fn swap_state_buffer(&mut self) {
        self.mark_dirty_states();
        self.buffers.swap(CURRENT_STATE_INDEX, NEXT_STATE_INDEX);
        for (offset, &(_, tpe)) in self.mutable_slot_states.iter().enumerate() {
            if !self.dirty_registry.states.contains(offset) {
                let current_slot = unsafe {
                    StateSlot::from_typed_slot_value(
                        current_state_buffer!(self).as_slice()[offset],
                        tpe,
                    )
                };
                let mut next_state_buffer = next_state_buffer_mut!(self);
                let mut next_slot = unsafe {
                    StateSlotMut::from_typed_slot_value(
                        &mut next_state_buffer.as_mut_slice()[offset],
                        tpe,
                    )
                };
                next_slot.clone_from(current_slot);
            }
        }
        // // SAFETY: non-init states in the output buffer will be overwritten in next step
        // unsafe {
        //     for &state in &self.mortal_states {
        //         next_state_buffer_mut!(self).reclaim_heap_allocated_expr(state)
        //     }
        // }
    }

    fn cached_states_shootdown(&mut self) {
        let mut all_dirty = FixedBitSet::with_capacity(self.mutable_slot_states.len());
        all_dirty.insert_range(..);
        self.dirty_registry.clear_and_track(all_dirty);
    }

    /// Inspect current state and next state to find those that are modified
    /// Schedule them to be re-computed at next `step` by adding them to `dirty_states`
    fn mark_dirty_states(&mut self) {
        let mut next_step_dirty_states = FixedBitSet::with_capacity(self.mutable_slot_states.len());
        for (offset, &(ref state, tpe)) in self.mutable_slot_states.iter().enumerate() {
            let (current_slot, next_slot) = unsafe {
                (
                    StateSlot::from_typed_slot_value(
                        current_state_buffer!(self).as_slice()[offset],
                        tpe,
                    ),
                    StateSlot::from_typed_slot_value(
                        next_state_buffer!(self).as_slice()[offset],
                        tpe,
                    ),
                )
            };
            if current_slot.ne(&next_slot) {
                if let Some(roots) = self.upstream_dependencies.get(&state.symbol) {
                    next_step_dirty_states.union_with(&roots);
                }
            }
        }
        self.dirty_registry.clear_and_track(next_step_dirty_states);
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum StateSlot<'a> {
    ThinBitVec(i64),
    WideBitVec(&'a BitVecValue),
    Array(&'a [i64]),
}

#[derive(PartialEq, Eq)]
enum StateSlotMut<'a> {
    ThinBitVec(&'a mut i64),
    WideBitVec(&'a mut BitVecValue),
    Array(&'a mut [i64]),
}

impl<'a> StateSlot<'a> {
    /// # Safety
    /// caller should guarantee that the value passed in points to a valid object of type `tpe`
    /// caller should make sure the returned slot will only be used within valid lifetime
    unsafe fn from_typed_slot_value(value: i64, tpe: expr::Type) -> Self {
        match tpe {
            expr::Type::BV(width) => match width {
                0..=64 => Self::ThinBitVec(value),
                _ => Self::WideBitVec(&*(value as *const BitVecValue)),
            },
            expr::Type::Array(ArrayType {
                index_width,
                data_width,
            }) => {
                assert!(index_width <= 12 && data_width <= 64);
                let len = 1 << index_width;
                Self::Array(std::slice::from_raw_parts(value as *const i64, len))
            }
        }
    }
}

impl<'a> StateSlotMut<'a> {
    /// # Safety
    /// caller should guarantee that the value passed in points to a valid object of type `tpe`
    /// caller should make sure the returned slot will only be used within valid lifetime
    ///
    /// An extra level of indirection will be followed for wide bv and array
    unsafe fn from_typed_slot_value(value: &'a mut i64, tpe: expr::Type) -> Self {
        match tpe {
            expr::Type::BV(width) => match width {
                0..=64 => Self::ThinBitVec(value),
                _ => Self::WideBitVec(&mut *(*value as *mut BitVecValue)),
            },
            expr::Type::Array(ArrayType {
                index_width,
                data_width,
            }) => {
                assert!(index_width <= 12 && data_width <= 64);
                let len = 1 << index_width;
                Self::Array(std::slice::from_raw_parts_mut(*value as *mut i64, len))
            }
        }
    }

    fn clone_from(&mut self, src: StateSlot) {
        match (self, src) {
            (Self::ThinBitVec(dst), StateSlot::ThinBitVec(src)) => dst.clone_from(&src),
            (Self::WideBitVec(dst), StateSlot::WideBitVec(src)) => dst.clone_from(src),
            (Self::Array(dst), StateSlot::Array(src)) => dst.copy_from_slice(src),
            _ => unreachable!(),
        }
    }
}

impl std::ops::Drop for JITEngine<'_> {
    fn drop(&mut self) {
        // SAFETY: invoked in drop, those states will no longer be accessed
        unsafe {
            current_state_buffer_mut!(self).reclaim_all();
            for &state in &self.immortal_states {
                next_state_buffer_mut!(self).reclaim_heap_allocated_expr(state);
            }
        }
    }
}

impl<B> StateBuffer<'_, B>
where
    B: std::borrow::BorrowMut<[i64]>,
    Self: StateBufferViewMut<i64>,
{
    fn try_replace_with_heap_reclaim(&mut self, expr: ExprRef, value: i64) {
        // SAFETY: old value is consumed here and not bookkept anywhere else, therefore can no longer be accessed
        unsafe {
            self.reclaim_heap_allocated_expr(expr);
        }
        *self.get_state_mut(expr) = value
    }

    /// # Safety
    /// the caller should guaranteed that the reclaimed expr is no longer accessed
    unsafe fn reclaim_heap_allocated_expr(&self, expr: ExprRef) {
        let value = *self.get_state_ref(expr);
        match expr.get_type(self.ctx) {
            expr::Type::BV(width) => {
                if width > 64 {
                    runtime::__dealloc_bv(value as *mut BitVecValue);
                }
            }
            expr::Type::Array(expr::ArrayType { index_width, .. }) => {
                runtime::__dealloc_array(value as *mut i64, index_width)
            }
        }
    }

    /// # Safety
    /// the caller should guaranteed that the reclaimed expr is no longer accessed
    unsafe fn reclaim_all(&self) {
        for &state in self.states_to_offset.keys() {
            self.reclaim_heap_allocated_expr(state);
        }
    }
}

impl Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: InitKind) {
        let mut generator = InitValueGenerator::from_kind(kind);

        for &state in self.states_to_offset.keys() {
            let tpe = state.get_type(self.ctx);
            let init_value = generator.gen(tpe);
            match init_value {
                baa::Value::BitVec(bv) => {
                    let bv = if bv.width() <= 64 {
                        bv.to_u64().unwrap() as i64
                    } else {
                        // SAFETY: &bv is a valid pointer to `BitVecValue`
                        unsafe { runtime::__clone_bv(&bv as *const BitVecValue) as i64 }
                    };
                    current_state_buffer_mut!(self).try_replace_with_heap_reclaim(state, bv)
                }
                baa::Value::Array(array) => {
                    let expr::Type::Array(expr::ArrayType {
                        index_width,
                        data_width,
                        ..
                    }) = tpe
                    else {
                        unreachable!()
                    };
                    assert!(
                        index_width <= 12 && data_width <= 64,
                        "currently only support dense array with thin bv"
                    );
                    debug_assert_eq!(1 << index_width, array.num_elements());
                    let buffer: Vec<_> = (0..array.num_elements())
                        .map(|idx| {
                            array
                                .select(&BitVecValue::from_u64(idx as u64, index_width))
                                .to_u64()
                                .unwrap() as i64
                        })
                        .collect();
                    let ptr = buffer.leak() as *mut [i64] as *mut i64 as i64;
                    current_state_buffer_mut!(self).try_replace_with_heap_reclaim(state, ptr)
                }
            }
        }

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                current_state_buffer_mut!(self).try_replace_with_heap_reclaim(state.symbol, ret);
            }
        }
        self.cached_states_shootdown();
    }

    fn step(&mut self) {
        for offset in self.dirty_registry.states.ones() {
            let state = &self.mutable_slot_states[offset].0;
            let next = state.next.unwrap();
            let ret = self.eval_expr(next);
            next_state_buffer_mut!(self).try_replace_with_heap_reclaim(state.symbol, ret);
        }
        self.swap_state_buffer();
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: BitVecValueRef<'b>) {
        assert!(matches!(self.ctx[expr], Expr::BVSymbol { .. }));
        assert!(value.width() <= 64);
        let value = value.to_u64().unwrap_or_else(|| {
            panic!(
                "unsupported bv value for jit based interpreter: {:?}",
                value
            )
        });
        *current_state_buffer_mut!(self).get_state_mut(expr) = value as i64;
        *next_state_buffer_mut!(self).get_state_mut(expr) = value as i64;

        if let Some(roots) = self.upstream_dependencies.get(&expr) {
            self.dirty_registry.register(&roots)
        }
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        let mut is_cached_symbol = false;
        let value = if let Some(&offset) = self.states_to_offset.get(&expr) {
            is_cached_symbol = true;
            current_state_buffer!(self).as_slice()[offset]
        } else {
            self.eval_expr(expr)
        };
        match expr.get_type(self.ctx) {
            expr::Type::Array(expr::ArrayType { index_width, .. }) => {
                // SAFETY: jit compiler guarantees that value points to a boxed slice with len 1 << index_width
                unsafe {
                    let words =
                        std::slice::from_raw_parts(value as *const baa::Word, 1 << index_width);
                    let ret = baa::Value::Array(words.into());
                    if !is_cached_symbol {
                        runtime::__dealloc_array(value as *mut i64, index_width);
                    }
                    ret
                }
            }
            expr::Type::BV(width) => match width {
                0..=64 => baa::Value::BitVec(BitVecValue::from_u64(value as u64, width)),
                _ =>
                // SAFETY: jit compiler guarantees that value is a pointer to wide bv allocated on heap
                unsafe {
                    if is_cached_symbol {
                        baa::Value::BitVec((*(value as *mut BitVecValue)).clone())
                    } else {
                        baa::Value::BitVec(*Box::from_raw(value as *mut BitVecValue))
                    }
                },
            },
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        todo!()
    }

    fn restore_snapshot(&mut self, _id: Self::SnapshotId) {
        todo!()
    }
}
