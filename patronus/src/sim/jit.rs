mod compiler;
mod runtime;

use super::Simulator;
use crate::expr::{self, *};
use crate::system::*;
use baa::*;
use compiler::{CompiledEvalFn, JITCompiler};
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

#[allow(dead_code)]
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
    compiled_code: FxHashMap<ExprRef, CompiledEvalFn>,
}

impl JITBackend {
    fn eval_expr(
        &mut self,
        expr: ExprRef,
        ctx: &expr::Context,
        input_state_buffer: &impl StateBufferView<i64>,
    ) -> i64 {
        let eval_fn = self.compiled_code.entry(expr).or_insert_with(|| {
            self.compiler
                .compile(ctx, expr, input_state_buffer)
                .unwrap_or_else(|err| panic!("fail to compile: `{:?}` due to {:?}", ctx[expr], err))
        });

        // SAFETY: jit compiler has not been dropped
        unsafe { eval_fn.call(input_state_buffer.as_slice()) }
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
            if let expr::Type::Array(expr::ArrayType {
                index_width,
                data_width,
            }) = state.get_type(ctx)
            {
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

                // allocate array buffer for both current and next state
                // this maintains the invariance that array states always points a valid boxed slice
                for state_buffer in &mut buffers {
                    let array = vec![0_i64; 1 << index_width].into_boxed_slice();
                    state_buffer[offset] = array.as_ptr() as i64;
                    std::mem::forget(array);
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

    fn current_state_buffer<'engine>(&'engine self) -> impl StateBufferView<i64> + 'engine {
        StateBuffer {
            buffer: &*self.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
        }
    }

    fn current_state_buffer_mut<'engine>(
        &'engine mut self,
    ) -> impl StateBufferViewMut<i64> + 'engine {
        StateBuffer {
            buffer: &mut *self.buffers[CURRENT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
        }
    }

    fn next_state_buffer_mut<'engine>(&'engine mut self) -> impl StateBufferViewMut<i64> + 'engine {
        StateBuffer {
            buffer: &mut *self.buffers[NEXT_STATE_INDEX],
            states_to_offset: &self.states_to_offset,
        }
    }

    fn eval_expr(&self, expr: ExprRef) -> i64 {
        self.backend
            .borrow_mut()
            .eval_expr(expr, self.ctx, &self.current_state_buffer())
    }

    fn update_state_buffer(&mut self) {
        self.buffers.swap(CURRENT_STATE_INDEX, NEXT_STATE_INDEX);
    }
}

impl std::ops::Drop for JITEngine<'_> {
    fn drop(&mut self) {
        for (&state, &offset) in &self.states_to_offset {
            if let expr::Type::Array(expr::ArrayType { index_width, .. }) = state.get_type(self.ctx)
            {
                for state_buffer in &mut self.buffers {
                    // SAFETY: the invariance we maintained for array states in the buffer guarantees that
                    // they all point to a valid boxed slice
                    unsafe {
                        runtime::__dealloc_array(state_buffer[offset] as *mut i64, index_width);
                    }
                }
            }
        }
    }
}

impl Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self) {
        for (state, offset) in self.states_to_offset.clone() {
            if let expr::Type::BV(..) = state.get_type(self.ctx) {
                self.current_state_buffer_mut().as_mut_slice()[offset] = 0;
            }
        }

        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                *self.current_state_buffer_mut().get_state_mut(state.symbol) = ret;
            }
        }
    }

    fn update(&mut self) {}
    fn step(&mut self) {
        for state in &self.sys.states {
            let Some(next) = state.next else { continue };
            let ret = self.eval_expr(next);
            match next.get_type(self.ctx) {
                expr::Type::BV(..) => {
                    *self.next_state_buffer_mut().get_state_mut(state.symbol) = ret
                }
                expr::Type::Array(expr::ArrayType { index_width, .. }) => {
                    let old_array_state = std::mem::replace(
                        self.next_state_buffer_mut().get_state_mut(state.symbol),
                        ret,
                    );
                    // SAFETY: the invariance we maintained for array states in the buffer guarantees that
                    // `old_array_state ` always points a valid boxed slice
                    unsafe { runtime::__dealloc_array(old_array_state as *mut i64, index_width) }
                }
            }
        }

        self.update_state_buffer();
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: BitVecValueRef<'b>) {
        assert!(matches!(self.ctx[expr], Expr::BVSymbol { .. }));
        *self.current_state_buffer_mut().get_state_mut(expr) =
            value.to_i64().unwrap_or_else(|| {
                panic!(
                    "unsupported bv value for jit based interpreter: {:?}",
                    value
                )
            });
    }

    fn get(&self, expr: ExprRef) -> Option<BitVecValue> {
        if let expr::Type::BV(width) = expr.get_type(self.ctx) {
            let value = self.eval_expr(expr);
            Some(BitVecValue::from_i64(value, width))
        } else {
            None
        }
    }

    fn get_element<'b>(&self, _expr: ExprRef, _index: BitVecValueRef<'b>) -> Option<BitVecValue> {
        todo!()
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
