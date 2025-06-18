mod bv_codegen;
mod compiler;
mod runtime;

use super::*;
use crate::expr::{self, *};
use crate::system::*;
use baa::*;
use compiler::*;
use cranelift::module::ModuleError;
use rustc_hash::FxHashMap;
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
#[allow(dead_code)]
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

pub struct JITEngine<'expr> {
    buffers: [Box<[i64]>; 2],
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
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

    fn step_transition_sys<B: StateBufferView<i64>>(
        &mut self,
        ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &B,
        output_state_buffer: &B,
    ) {
        let eval_fn = self.compiled_transition_sys.get_or_insert_with(|| {
            self.compiler
                .compile_transition_sys(ctx, sys, input_state_buffer, output_state_buffer)
                .unwrap_or_else(|err| {
                    panic!("fail to compile transition step function, due to {:?}", err)
                })
        });

        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(
                input_state_buffer.as_slice(),
                output_state_buffer.as_slice(),
            )
        }
    }
}

impl<'expr> JITEngine<'expr> {
    pub fn new(ctx: &'expr expr::Context, sys: &'expr TransitionSystem) -> JITEngine<'expr> {
        let mut states_to_offset: FxHashMap<ExprRef, usize> = FxHashMap::default();
        for state in sys
            .states
            .iter()
            .map(|state| state.symbol)
            .chain(sys.inputs.iter().copied())
        {
            let offset = states_to_offset.len();
            states_to_offset.entry(state).or_insert(offset);
        }

        let mut buffers: [Box<[i64]>; 2] =
            std::array::from_fn(|_| vec![0_i64; states_to_offset.len()].into_boxed_slice());
        for (&state, &offset) in &states_to_offset {
            match state.get_type(ctx) {
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

                    // this maintains the invariance that array states in current buffer always points to a valid boxed slice
                    buffers[CURRENT_STATE_INDEX][offset] =
                        vec![0_i64; 1 << index_width].leak() as *mut [i64] as *mut i64 as i64;
                }
                expr::Type::BV(width) => {
                    if width > 64 {
                        // this maintains the invariance that wide bv in current buffer always points to a valid baa:BitVecValue
                        let bv = Box::new(BitVecValue::zero(width));
                        buffers[CURRENT_STATE_INDEX][offset] = Box::leak(bv) as *mut _ as i64;
                    }
                }
            }
        }

        Self {
            backend: RefCell::default(),
            buffers,
            ctx,
            sys,
            states_to_offset,
            step_count: 0,
        }
    }

    fn current_state_buffer(&self) -> StateBuffer<'_, &[i64]> {
        StateBuffer {
            buffer: &*self.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
            ctx: self.ctx,
        }
    }

    fn current_state_buffer_mut(&mut self) -> StateBuffer<'_, &mut [i64]> {
        StateBuffer {
            buffer: &mut *self.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
            ctx: self.ctx,
        }
    }

    fn next_state_buffer_mut(&mut self) -> StateBuffer<'_, &mut [i64]> {
        StateBuffer {
            buffer: &mut *self.buffers[NEXT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
            ctx: self.ctx,
        }
    }

    fn next_state_buffer(&self) -> StateBuffer<'_, &[i64]> {
        StateBuffer {
            buffer: &*self.buffers[NEXT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
            ctx: self.ctx,
        }
    }

    fn eval_expr(&self, expr: ExprRef) -> i64 {
        self.backend
            .borrow_mut()
            .eval_expr(expr, self.ctx, &self.current_state_buffer())
    }

    fn step_transition_sys(&self) {
        self.backend.borrow_mut().step_transition_sys(
            self.ctx,
            self.sys,
            &self.current_state_buffer(),
            &self.next_state_buffer(),
        );
    }

    /// Maintains the invariance that before each step, the heap resources allocated
    /// in the output buffer are reclaimed
    fn swap_state_buffer(&mut self) {
        self.buffers.swap(CURRENT_STATE_INDEX, NEXT_STATE_INDEX);
        // SAFETY: states in the output buffer will be overwritten in next step
        unsafe { self.next_state_buffer_mut().reclaim_all() }
    }
}

impl std::ops::Drop for JITEngine<'_> {
    fn drop(&mut self) {
        // SAFETY: invoked in drop, those states will no longer be accessed
        unsafe {
            self.current_state_buffer_mut().reclaim_all();
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

        for state in self.states_to_offset.clone().into_keys() {
            let tpe = state.get_type(self.ctx);
            let init_value = generator.gen(tpe);
            match init_value {
                baa::Value::BitVec(bv) => {
                    let bv = if bv.width() < 64 {
                        bv.to_u64().unwrap() as i64
                    } else {
                        // SAFETY: &bv is a valid pointer to `BitVecValue`
                        unsafe { runtime::__clone_bv(&bv as *const BitVecValue) as i64 }
                    };
                    self.current_state_buffer_mut()
                        .try_replace_with_heap_reclaim(state, bv)
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
                    self.current_state_buffer_mut()
                        .try_replace_with_heap_reclaim(state, ptr)
                }
            }
        }

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                self.current_state_buffer_mut()
                    .try_replace_with_heap_reclaim(state.symbol, ret);
            }
        }
    }

    fn step(&mut self) {
        self.step_transition_sys();
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
        *self.current_state_buffer_mut().get_state_mut(expr) = value as i64;
    }

    fn get(&self, expr: ExprRef) -> baa::Value {
        let mut is_cached_symbol = false;
        let value = if let Some(&offset) = self.states_to_offset.get(&expr) {
            is_cached_symbol = true;
            self.current_state_buffer().as_slice()[offset]
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
