mod compiler;

use super::Simulator;
use crate::expr::{self, *};
use crate::system::*;
use baa::*;
use compiler::{CompiledEvalFn, JITCompiler};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::ModuleError;
use std::collections::HashMap;

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

struct StateBufferView<'engine> {
    buffer: &'engine [i64],
    states_to_offset: &'engine HashMap<ExprRef, usize>,
}

impl StateBufferView<'_> {
    fn get_state_offset(&self, expr: ExprRef) -> usize {
        self.states_to_offset[&expr]
    }

    fn get_state_ref(&self, expr: ExprRef) -> &i64 {
        &self.buffer[self.get_state_offset(expr)]
    }
}

pub struct JITEngine<'expr> {
    current_states_buffer: Vec<i64>,
    next_states_buffer: Vec<i64>,
    compiler: JITCompiler,
    expr_ctx: &'expr expr::Context,
    sys: &'expr TransitionSystem,
    compiled_code: HashMap<ExprRef, CompiledEvalFn>,
    states_to_offset: HashMap<ExprRef, usize>,
    step_count: u64,
}

impl<'expr> JITEngine<'expr> {
    pub fn launch_instance(
        expr_ctx: &'expr expr::Context,
        sys: &'expr TransitionSystem,
    ) -> Option<JITEngine<'expr>> {
        let builder = JITBuilder::new(cranelift::module::default_libcall_names()).ok()?;
        let module = JITModule::new(builder);
        let states_to_offset: HashMap<_, _> = sys
            .states
            .iter()
            .flat_map(|state| {
                std::iter::once(state.symbol)
                    .chain(state.init)
                    .chain(state.next)
            })
            .enumerate()
            .map(|(idx, expr)| (expr, idx))
            .collect();
        let num_states = states_to_offset.len();

        Some(Self {
            compiler: JITCompiler::new(module),
            current_states_buffer: vec![0; num_states],
            next_states_buffer: vec![0; num_states],
            expr_ctx,
            sys,
            compiled_code: HashMap::default(),
            states_to_offset,
            step_count: 0,
        })
    }

    fn current_states_buffer_view(&self) -> StateBufferView<'_> {
        StateBufferView {
            buffer: &self.current_states_buffer,
            states_to_offset: &self.states_to_offset,
        }
    }

    fn eval_expr(&mut self, expr: ExprRef) {
        let eval_fn = self.compiled_code.entry(expr).or_insert_with(|| {
            let input_states_buffer = StateBufferView {
                buffer: &self.current_states_buffer,
                states_to_offset: &self.states_to_offset,
            };
            let output_states_buffer = StateBufferView {
                buffer: &self.next_states_buffer,
                states_to_offset: &self.states_to_offset,
            };
            self.compiler
                .compile(
                    self.expr_ctx,
                    expr,
                    input_states_buffer,
                    output_states_buffer,
                )
                .unwrap()
        });

        // SAFETY: jit compiler has not been dropped
        unsafe {
            eval_fn.call(&self.current_states_buffer, &mut self.next_states_buffer);
        }
    }

    fn update_states_buffer(&mut self) {
        for state in &self.sys.states {
            if let Some(next) = state.next {
                self.current_states_buffer[self.states_to_offset[&state.symbol]] =
                    self.next_states_buffer[self.states_to_offset[&next]]
            }
        }
    }
}

impl Simulator for JITEngine<'_> {
    type SnapshotId = u32;
    fn init(&mut self) {
        self.current_states_buffer.fill(0);
        for state in &self.sys.states {
            if let Some(init) = state.init {
                self.eval_expr(init);
            }
        }
        self.update_states_buffer()
    }

    fn update(&mut self) {}
    fn step(&mut self) {
        self.sys.states.iter().for_each(|s| {
            if let Some(next) = s.next {
                self.eval_expr(next)
            }
        });
        self.update_states_buffer();
        self.step_count += 1;
    }

    fn set<'b>(&mut self, _expr: ExprRef, _value: impl Into<BitVecValueRef<'b>>) {
        todo!()
    }

    fn get(&self, expr: ExprRef) -> Option<BitVecValue> {
        let current_states_buffer = self.current_states_buffer_view();
        let value = *current_states_buffer.get_state_ref(expr);
        if let expr::Type::BV(width) = self.expr_ctx[expr].get_type(self.expr_ctx) {
            Some(BitVecValue::from_i64(value, width))
        } else {
            None
        }
    }

    fn get_element<'b>(
        &self,
        _expr: ExprRef,
        _index: impl Into<BitVecValueRef<'b>>,
    ) -> Option<BitVecValue> {
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
