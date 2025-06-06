mod compiler;

use super::Simulator;
use crate::expr::{self, *};
use crate::system::*;
use baa::*;
use compiler::{CompiledEvalFn, JITCompiler};
use cranelift::jit::{JITBuilder, JITModule};
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

struct BVStateBuffer<'engine, B> {
    buffer: B,
    states_to_offset: &'engine FxHashMap<ExprRef, usize>,
}

impl<B> StateBufferView<i64> for BVStateBuffer<'_, B>
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

impl<B> StateBufferViewMut<i64> for BVStateBuffer<'_, B>
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

const BV_CURRENT_STATE_INDEX: usize = 0;
const BV_NEXT_STATE_INDEX: usize = 1;

pub struct JITEngine<'expr> {
    buffers: [Vec<i64>; 2],
    ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    /// interior mutability for lazy compilation triggered by `Simulator::get`
    backend: RefCell<JITBackend>,
    states_to_offset: FxHashMap<ExprRef, usize>,
    step_count: u64,
}

struct JITBackend {
    compiler: JITCompiler,
    compiled_code: FxHashMap<ExprRef, CompiledEvalFn>,
}

impl JITBackend {
    fn new() -> Self {
        let builder = JITBuilder::new(cranelift::module::default_libcall_names())
            .unwrap_or_else(|_| panic!("fail to launch jit instance"));
        let module = JITModule::new(builder);
        Self {
            compiler: JITCompiler::new(module),
            compiled_code: FxHashMap::default(),
        }
    }
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
        for state in sys.states.iter().flat_map(|state| {
            std::iter::once(state.symbol)
                .chain(state.init)
                .chain(state.next)
        }) {
            let offset = states_to_offset.len();
            states_to_offset.entry(state).or_insert(offset);
        }
        Self {
            backend: RefCell::new(JITBackend::new()),
            buffers: std::array::from_fn(|_| vec![0; states_to_offset.len()]),
            ctx,
            sys,
            states_to_offset,
            step_count: 0,
        }
    }

    fn current_bv_state_buffer(&self) -> BVStateBuffer<&[i64]> {
        BVStateBuffer {
            buffer: self.buffers[BV_CURRENT_STATE_INDEX].as_slice(),
            states_to_offset: &self.states_to_offset,
        }
    }

    fn current_bv_state_buffer_mut(&mut self) -> BVStateBuffer<&mut [i64]> {
        BVStateBuffer {
            buffer: self.buffers[BV_CURRENT_STATE_INDEX].as_mut_slice(),
            states_to_offset: &self.states_to_offset,
        }
    }

    fn next_bv_state_buffer_mut(&mut self) -> BVStateBuffer<&mut [i64]> {
        BVStateBuffer {
            buffer: self.buffers[BV_NEXT_STATE_INDEX].as_mut_slice(),
            states_to_offset: &self.states_to_offset,
        }
    }

    fn eval_expr(&self, expr: ExprRef) -> i64 {
        self.backend
            .borrow_mut()
            .eval_expr(expr, &self.ctx, &self.current_bv_state_buffer())
    }

    fn update_state_buffer(&mut self) {
        self.buffers
            .swap(BV_CURRENT_STATE_INDEX, BV_NEXT_STATE_INDEX)
    }
}

impl Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self) {
        self.current_bv_state_buffer_mut().as_mut_slice().fill(0);
        for state in &self.sys.states {
            if let Some(init) = state.init {
                let ret = self.eval_expr(init);
                *self
                    .current_bv_state_buffer_mut()
                    .get_state_mut(state.symbol) = ret;
            }
        }
    }

    fn update(&mut self) {}
    fn step(&mut self) {
        self.sys.states.iter().for_each(|s| {
            if let Some(next) = s.next {
                let ret = self.eval_expr(next);
                *self.next_bv_state_buffer_mut().get_state_mut(s.symbol) = ret;
            }
        });
        self.update_state_buffer();
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: BitVecValueRef<'b>) {
        assert!(matches!(self.ctx[expr], Expr::BVSymbol { .. }));
        *self.current_bv_state_buffer_mut().get_state_mut(expr) =
            value.to_i64().unwrap_or_else(|| {
                panic!(
                    "unsupported bv value for jit based interpreter: {:?}",
                    value
                )
            });
    }

    fn get(&self, expr: ExprRef) -> Option<BitVecValue> {
        if let expr::Type::BV(width) = self.ctx[expr].get_type(self.ctx) {
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
