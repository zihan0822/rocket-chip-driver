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
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::sync::LazyLock;

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

/// Bit vector with width less than `THIN_BV_MAX_WIDTH` is stored as Rust primitive type.
/// Otherwise, it is stored as `baa::BitVecValue`
const THIN_BV_MAX_WIDTH: u32 = 64;
const CURRENT_STATE_INDEX: usize = 0;
const NEXT_STATE_INDEX: usize = 1;
/// Minimum dirty percentage of output states that will trigger batched update mode
const BATCHED_UPDATE_THRESHOLD: f64 = 0.6;
/// Only when this environment variable is set and the threshold condition is met, dynamic mode switch will be turned on.
static DYNAMIC_MODE_SWITCH: LazyLock<bool> =
    LazyLock::new(|| std::env::var("DYNAMIC_MODE_SWITCH").is_ok_and(|enable| enable.eq("1")));
/// Minimum number of expr nodes that will enable dynamic switching between per-expr and batched update mode.
/// If the number of expr nodes is less than or equal to this, JIT will always use batched update mode.
/// TODO: better heuristics than simple expr nodes count
const DYNAMIC_MODE_SWITCH_THRESHOLD: usize = 1500;

enum DirtyUpdatePolicy {
    Sparse,
    Batched,
}
struct DirtyStateRegistry {
    states: FixedBitSet,
    /// Currently used in `mark_dirty_states` to store the dirty states for next step to avoid heap allocation
    scratch_states: FixedBitSet,
    num_total_states: f64,
}

impl DirtyStateRegistry {
    fn new(init_states: FixedBitSet, num_total_states: usize) -> Self {
        Self {
            states: init_states.clone(),
            scratch_states: FixedBitSet::with_capacity(num_total_states),
            num_total_states: num_total_states as f64,
        }
    }

    #[inline]
    fn register(&mut self, dirty_states: &FixedBitSet) {
        self.states.union_with(dirty_states);
    }

    fn select_update_policy(&self) -> DirtyUpdatePolicy {
        if self.dirty_percentage() >= BATCHED_UPDATE_THRESHOLD {
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
    /// Interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    /// For each leaf state, tracks all root state expr that transitively depends on it
    upstream_dependents: FxHashMap<ExprRef, FixedBitSet>,
    /// Maintains set of states that need to be recomputed at next step
    dirty_registry: DirtyStateRegistry,
    /// States corresponding to the first `sys.states.len()` expr in the state buffer
    /// types are cached for better perf
    mutable_slot_states: Vec<(State, expr::Type)>,
    states_to_offset: FxHashMap<ExprRef, usize>,
    step_count: u64,
    /// Whether dynamic switching is enabled is determined by the number of expr nodes.
    /// When enabled, JIT will switch between per-expr and batched update mode in each `step()` according to the dirty
    /// percetange of output states.
    dynamic_update_mode_switching_enabled: bool,
    snapshots: Vec<Box<[i64]>>,
}

#[derive(Default)]
struct JITBackend {
    compiler: JITCompiler,
    compiled_transition_sys: Option<EvalBatchedExprWithUpdate>,
    compiled_expr_eval: FxHashMap<ExprRef, EvalSingleExprWithUpdate>,
}

impl JITBackend {
    /// # Safety
    /// The caller should guarantee that `ret_placeholder` is a valid pointer to object of the same type as `expr`
    unsafe fn eval_expr(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &impl StateBufferView<i64>,
        ret_placeholder: *mut (),
    ) {
        unsafe {
            let eval_fn = self.compiled_expr_eval.entry(expr).or_insert_with(|| {
                self.compiler
                    .compile_expr(ctx, expr, input_state_buffer)
                    .unwrap_or_else(|err| {
                        panic!("fail to compile: `{:?}` due to {:?}", ctx[expr], err)
                    })
            });

            // SAFETY: jit compiler has not been dropped
            eval_fn.call(input_state_buffer.as_slice(), ret_placeholder as *mut i64);
        }
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
                    panic!("fail to compile transition step function, due to {err:?}")
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
            buffer: &*$engine.buffers[NEXT_STATE_INDEX],
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

impl ArrayType {
    fn alloc(&self) -> *mut () {
        if self.data_width <= THIN_BV_MAX_WIDTH {
            runtime::__alloc_array(self.index_width, 0) as _
        } else {
            // SAFETY: default value comes from a valid BitVecValue on stack
            unsafe {
                runtime::__alloc_array_of_wide_bv(
                    self.index_width,
                    &baa::BitVecValue::zero(self.data_width),
                ) as _
            }
        }
    }

    /// # Safety
    /// The caller should guarantee that the array `ptr` points to is allocated by `ArrayType::alloc` and has the correct type
    unsafe fn dealloc(&self, ptr: *mut ()) {
        unsafe {
            if self.data_width <= THIN_BV_MAX_WIDTH {
                runtime::__dealloc_array(ptr as *mut i64, self.index_width);
            } else {
                runtime::__dealloc_array_of_wide_bv(
                    ptr as *mut *mut baa::BitVecValue,
                    self.index_width,
                )
            }
        }
    }

    /// # Safety
    /// The caller should guarantee that the array `ptr` points to is allocated by `ArrayType::alloc` and has the correct type
    unsafe fn clone(&self, ptr: *const ()) -> *mut () {
        unsafe {
            if self.data_width <= THIN_BV_MAX_WIDTH {
                runtime::__clone_array(ptr as *const i64, self.index_width) as _
            } else {
                runtime::__clone_array_of_wide_bv(
                    ptr as *const *const baa::BitVecValue,
                    self.index_width,
                ) as _
            }
        }
    }
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

        let buffers: [Box<[i64]>; 2] =
            std::array::from_fn(|_| vec![0_i64; states_to_offset.len()].into_boxed_slice());

        let mut init_states = FixedBitSet::with_capacity(mutable_slot_states.len());
        init_states.insert_range(..);
        let dirty_registry = DirtyStateRegistry::new(init_states, mutable_slot_states.len());
        let dynamic_update_mode_switching_enabled =
            *DYNAMIC_MODE_SWITCH && ctx.exprs.len() > DYNAMIC_MODE_SWITCH_THRESHOLD;

        let mut engine = Self {
            backend: RefCell::default(),
            buffers,
            ctx,
            sys,
            states_to_offset,
            mutable_slot_states,
            upstream_dependents: FxHashMap::default(),
            dirty_registry,
            step_count: 0,
            dynamic_update_mode_switching_enabled,
            snapshots: Vec::default(),
        };
        engine.bootstrap_state_buffers();
        if dynamic_update_mode_switching_enabled {
            engine.find_leaf_states_upstream_dep();
        }
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
                    .upstream_dependents
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
        for (&state, &offset) in &self.states_to_offset {
            for buffer in &mut self.buffers {
                match state.get_type(self.ctx) {
                    expr::Type::Array(array_ty) => {
                        buffer[offset] = array_ty.alloc() as i64;
                    }
                    expr::Type::BV(width) => {
                        if width > 64 {
                            buffer[offset] = runtime::__alloc_bv(width) as i64;
                        }
                    }
                }
            }
        }
    }

    /// Evaluates expression binded to slot at `offset` and saves the result at the same position in the next state buffer.
    /// This function directly takes slot offset as parameter instead of `ExprRef` to avoid `states_to_offset` search overhead.
    fn eval_expr_at_slot(&self, offset: usize) {
        let &(ref state, tpe) = &self.mutable_slot_states[offset];
        let ret_placeholder = if matches!(tpe, expr::Type::BV(width) if width  <= THIN_BV_MAX_WIDTH)
        {
            &next_state_buffer!(self).as_slice()[offset] as *const _ as *mut ()
        } else {
            next_state_buffer!(self).as_slice()[offset] as *mut ()
        };
        // SAFETY: `ret_placeholder` is obtained from `next_state_buffer` at the same slot, so it points to
        // an object of correct type. There is no alias xor mut conflit here, `ret_placeholder` is guaranteed to not
        // overlap with `current_state_buffer`
        unsafe {
            self.eval_expr_with_ret_placeholder(state.next.unwrap(), ret_placeholder);
        }
    }

    /// Computes expressions that do not bind to a mutable state slot.
    /// Interpretation of the returned value varies depending on the expression type.
    /// For wide bit vector and array, the returned value is a pointer to leaked heap allocated object.
    fn eval_non_state_expr(&self, expr: ExprRef) -> i64 {
        match expr.get_type(self.ctx) {
            expr::Type::BV(width) => {
                if width <= THIN_BV_MAX_WIDTH {
                    let mut ret_placeholder: i64 = 0;
                    // SAFETY: ref mut of stack allocated `i64` for thin bitvector
                    unsafe {
                        self.eval_expr_with_ret_placeholder(
                            expr,
                            &mut ret_placeholder as *mut _ as *mut (),
                        );
                    }
                    ret_placeholder
                } else {
                    let bv = runtime::__alloc_bv(width) as *mut ();
                    // SAFETY: heap allocated wide bitvector
                    unsafe {
                        self.eval_expr_with_ret_placeholder(expr, bv);
                    }
                    bv as i64
                }
            }
            expr::Type::Array(array_ty) => {
                unsafe {
                    // SAFETY: heap allocated array
                    let array = array_ty.alloc();
                    self.eval_expr_with_ret_placeholder(expr, array);
                    array as i64
                }
            }
        }
    }

    /// # Safety
    /// Follows the same requirement as `JITBackend::expr_expr`
    unsafe fn eval_expr_with_ret_placeholder(&self, expr: ExprRef, ret_placeholder: *mut ()) {
        unsafe {
            self.backend.borrow_mut().eval_expr(
                expr,
                self.ctx,
                &current_state_buffer!(self),
                ret_placeholder,
            )
        }
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
        self.cached_states_shootdown();
    }

    fn swap_state_buffer(&mut self) {
        if !self.dynamic_update_mode_switching_enabled {
            self.buffers.swap(CURRENT_STATE_INDEX, NEXT_STATE_INDEX);
            return;
        }
        self.mark_dirty_states();
        let previous_dirty_states = &self.dirty_registry.states;
        // If all mutable states are marked dirty, which can be caused by `cached_states_shootdown` when
        // the very last update strategy we choose is `step_transition_sys`, we optimize state buffer updating by directly swapping
        // current and next buffer
        if previous_dirty_states.is_full() {
            self.buffers.swap(CURRENT_STATE_INDEX, NEXT_STATE_INDEX);
        } else {
            let [current_state_buffer, next_state_buffer] = self
                .buffers
                .get_disjoint_mut([CURRENT_STATE_INDEX, NEXT_STATE_INDEX])
                .unwrap();
            for offset in previous_dirty_states.ones() {
                std::mem::swap(
                    &mut current_state_buffer[offset],
                    &mut next_state_buffer[offset],
                );
            }
        }
        std::mem::swap(
            &mut self.dirty_registry.states,
            &mut self.dirty_registry.scratch_states,
        );
    }

    fn cached_states_shootdown(&mut self) {
        self.dirty_registry.states.insert_range(..);
    }

    /// Inspect current state and next state to find those that are modified
    /// Schedule them to be re-computed at next `step` by adding them to `dirty_states`
    fn mark_dirty_states(&mut self) {
        let states_require_reexamine = &self.dirty_registry.states;
        let next_step_dirty_states = &mut self.dirty_registry.scratch_states;
        next_step_dirty_states.clear();
        let (current_state_buffer, next_state_buffer) =
            (current_state_buffer!(self), next_state_buffer!(self));
        for offset in states_require_reexamine.ones() {
            let &(ref state, tpe) = &self.mutable_slot_states[offset];
            let (current_slot, next_slot) = unsafe {
                (
                    StateSlot::from_typed_slot_value(&current_state_buffer.as_slice()[offset], tpe),
                    StateSlot::from_typed_slot_value(&next_state_buffer.as_slice()[offset], tpe),
                )
            };
            if current_slot.ne(&next_slot) {
                if let Some(roots) = self.upstream_dependents.get(&state.symbol) {
                    next_step_dirty_states.union_with(roots);
                }
            }
        }
    }

    fn clone_state_buffer(&self, src: &impl StateBufferView<i64>) -> Box<[i64]> {
        let mut dst = vec![0_i64; self.states_to_offset.len()];
        for (state, &offset) in &self.states_to_offset {
            let value = src.as_slice()[offset];
            match state.get_type(self.ctx) {
                expr::Type::BV(width) => {
                    if width <= THIN_BV_MAX_WIDTH {
                        dst[offset] = value;
                    } else {
                        // SAFETY: `value` coming from state buffer is guaranteed to be valid
                        unsafe {
                            dst[offset] = runtime::__clone_bv(value as *const BitVecValue) as i64;
                        }
                    }
                }
                expr::Type::Array(array_ty) => unsafe {
                    // SAFETY: `value` coming from state buffer is guaranteed to be valid
                    dst[offset] = array_ty.clone(value as *const ()) as i64;
                },
            }
        }
        dst.into_boxed_slice()
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum StateSlot<'a> {
    ThinBitVec(&'a i64),
    WideBitVec(&'a BitVecValue),
    Array(&'a [i64]),
}

impl<'a> StateSlot<'a> {
    /// # Safety
    /// caller should guarantee that the value passed in points to a valid object of type `tpe`
    /// caller should make sure the returned slot will only be used within valid lifetime
    ///
    /// An extra level of indirection is followed for wide bit vector and array.
    unsafe fn from_typed_slot_value(value: &'a i64, tpe: expr::Type) -> Self {
        unsafe {
            match tpe {
                expr::Type::BV(width) => match width {
                    0..=64 => Self::ThinBitVec(value),
                    _ => Self::WideBitVec(&*(*value as *const BitVecValue)),
                },
                expr::Type::Array(ArrayType { index_width, .. }) => {
                    let len = 1 << index_width;
                    Self::Array(std::slice::from_raw_parts(*value as *const i64, len))
                }
            }
        }
    }
}

impl std::ops::Drop for JITEngine<'_> {
    fn drop(&mut self) {
        // SAFETY: invoked in drop, those states will no longer be accessed
        unsafe {
            current_state_buffer_mut!(self).reclaim_all();
            next_state_buffer_mut!(self).reclaim_all();
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
        unsafe {
            let value = *self.get_state_ref(expr);
            match expr.get_type(self.ctx) {
                expr::Type::BV(width) => {
                    if width > THIN_BV_MAX_WIDTH {
                        runtime::__dealloc_bv(value as *mut BitVecValue);
                    }
                }
                expr::Type::Array(array_ty) => {
                    array_ty.dealloc(value as *mut ());
                }
            }
        }
    }

    /// # Safety
    /// the caller should guaranteed that the reclaimed expr is no longer accessed
    unsafe fn reclaim_all(&self) {
        unsafe {
            for &state in self.states_to_offset.keys() {
                self.reclaim_heap_allocated_expr(state);
            }
        }
    }
}

impl Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self, kind: InitKind) {
        let mut generator = InitValueGenerator::from_kind(kind);

        for &state in self.states_to_offset.keys() {
            let tpe = state.get_type(self.ctx);
            let init_value = generator.generate(tpe);
            match init_value {
                baa::Value::BitVec(bv) => {
                    let bv = if bv.width() <= THIN_BV_MAX_WIDTH {
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
                    }) = tpe
                    else {
                        unreachable!()
                    };
                    debug_assert_eq!(1 << index_width, array.num_elements());
                    let buffer: Vec<_> = (0..array.num_elements())
                        .map(|idx| {
                            let src_element =
                                array.select(&BitVecValue::from_u64(idx as u64, index_width));
                            if data_width <= THIN_BV_MAX_WIDTH {
                                src_element.to_u64().unwrap() as i64
                            } else {
                                Box::leak(Box::new(src_element)) as *mut baa::BitVecValue as i64
                            }
                        })
                        .collect();
                    let ptr = buffer.leak() as *mut [i64] as *mut i64 as i64;
                    current_state_buffer_mut!(self).try_replace_with_heap_reclaim(state, ptr)
                }
            }
        }

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_non_state_expr(init);
                current_state_buffer_mut!(self).try_replace_with_heap_reclaim(state.symbol, ret);
            }
        }
        self.cached_states_shootdown();
    }

    fn step(&mut self) {
        if !self.dynamic_update_mode_switching_enabled
            || matches!(
                self.dirty_registry.select_update_policy(),
                DirtyUpdatePolicy::Batched
            )
        {
            self.step_transition_sys();
        } else {
            self.dirty_registry
                .states
                .ones()
                .for_each(|offset| self.eval_expr_at_slot(offset));
        }
        self.swap_state_buffer();
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: BitVecValueRef<'b>) {
        let expr::Type::BV(width) = expr.get_type(self.ctx) else {
            unreachable!()
        };
        if width <= THIN_BV_MAX_WIDTH {
            let value = value.to_u64().unwrap();
            *current_state_buffer_mut!(self).get_state_mut(expr) = value as i64;
            *next_state_buffer_mut!(self).get_state_mut(expr) = value as i64;
        } else {
            // XXX: currently `runtime::__clone_bv` only supports raw pointer to `BitVecValue` as parameter
            let value: BitVecValue = value.into();
            unsafe {
                *current_state_buffer_mut!(self).get_state_mut(expr) =
                    runtime::__clone_bv(&value as *const BitVecValue) as i64;
                *next_state_buffer_mut!(self).get_state_mut(expr) =
                    runtime::__clone_bv(&value as *const BitVecValue) as i64;
            }
        }

        if let Some(roots) = self.upstream_dependents.get(&expr) {
            self.dirty_registry.register(roots)
        }
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        let mut is_cached_symbol = false;
        let tpe;
        let value = if let Some(&offset) = self.states_to_offset.get(&expr) {
            is_cached_symbol = true;
            tpe = self.mutable_slot_states[offset].1;
            current_state_buffer!(self).as_slice()[offset]
        } else {
            tpe = expr.get_type(self.ctx);
            self.eval_non_state_expr(expr)
        };
        match tpe {
            expr::Type::Array(
                array_ty @ ArrayType {
                    index_width,
                    data_width,
                },
            ) => {
                // SAFETY: jit compiler guarantees that `value` points to a valid array with correct type
                unsafe {
                    let ret = if index_width <= THIN_BV_MAX_WIDTH {
                        let words =
                            std::slice::from_raw_parts(value as *const baa::Word, 1 << index_width);
                        baa::Value::Array(words.into())
                    } else {
                        let mut array = baa::ArrayValue::new_dense(
                            index_width,
                            &baa::BitVecValue::zero(data_width),
                        );
                        std::slice::from_raw_parts(
                            value as *const baa::BitVecValue,
                            1 << index_width,
                        )
                        .iter()
                        .enumerate()
                        .for_each(|(idx, bv)| {
                            array.store(&BitVecValue::from_u64(idx as u64, index_width), bv);
                        });
                        baa::Value::Array(array)
                    };
                    if !is_cached_symbol {
                        array_ty.dealloc(value as *mut ());
                    }
                    ret
                }
            }
            expr::Type::BV(width) => {
                if width <= THIN_BV_MAX_WIDTH {
                    baa::Value::BitVec(BitVecValue::from_u64(value as u64, width))
                } else {
                    // SAFETY: jit compiler guarantees that value is a pointer to wide bv allocated on heap
                    unsafe {
                        if is_cached_symbol {
                            baa::Value::BitVec((*(value as *mut BitVecValue)).clone())
                        } else {
                            baa::Value::BitVec(*Box::from_raw(value as *mut BitVecValue))
                        }
                    }
                }
            }
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let snapshot = self.clone_state_buffer(&current_state_buffer!(self));
        let id = self.snapshots.len() as u32;
        self.snapshots.push(snapshot);
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        std::mem::swap(
            &mut self.buffers[CURRENT_STATE_INDEX],
            &mut self.snapshots[id as usize],
        );
        let restored_snapshot = self.clone_state_buffer(&current_state_buffer!(self));
        let dropped_snapshot =
            std::mem::replace(&mut self.snapshots[id as usize], restored_snapshot);
        // SAFETY: `dropped_snapshot` is taken from current state buffer, all its elements are guaranteed to point to a valid heap allocated object
        unsafe {
            StateBuffer {
                buffer: dropped_snapshot,
                states_to_offset: &self.states_to_offset,
                ctx: self.ctx,
            }
            .reclaim_all();
        }
    }
}
