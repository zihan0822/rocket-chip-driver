use super::{JITResult, StateBufferView};
use crate::expr::{self, *};

use baa::BitVecOps;
use cranelift::codegen::ir::{self, condcodes::IntCC};
use cranelift::jit::JITModule;
use cranelift::module::Module;
use cranelift::prelude::*;
use smallvec::SmallVec;

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

impl JITCompiler {
    pub(super) fn new(module: JITModule) -> Self {
        Self { module }
    }

    pub(super) fn compile(
        &mut self,
        expr_ctx: &expr::Context,
        root_expr: ExprRef,
        input_state_buffer: &impl StateBufferView<i64>,
    ) -> JITResult<CompiledEvalFn> {
        // signature: fn(input, output, prev_state, next_state)
        let mut cranelift_ctx = self.module.make_context();
        cranelift_ctx.func.signature.params = vec![ir::AbiParam::new(types::I64)];
        cranelift_ctx.func.signature.returns = vec![ir::AbiParam::new(types::I64)];
        cranelift_ctx.func.signature.call_conv = isa::CallConv::SystemV;

        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut cranelift_ctx.func, &mut fn_builder_ctx);
        let entry_block = fn_builder.create_block();
        fn_builder.append_block_params_for_function_params(entry_block);
        fn_builder.switch_to_block(entry_block);
        fn_builder.seal_block(entry_block);

        let codegen_ctx = CodeGenContext {
            fn_builder,
            block_id: entry_block,
            expr_ctx,
            root_expr,
            input_state_buffer,
            int: types::I64,
        };

        codegen_ctx.codegen();

        let mut buffer = String::new();
        codegen::write::write_function(&mut buffer, &cranelift_ctx.func).unwrap();
        eprintln!("{}", buffer);

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
    block_id: Block,
    expr_ctx: &'expr expr::Context,
    root_expr: ExprRef,
    input_state_buffer: &'engine dyn StateBufferView<i64>,
    int: cranelift::prelude::Type,
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen(mut self) {
        let ret = self.mock_interpret();
        self.fn_builder.ins().return_(&[ret]);
        self.fn_builder.finalize();
    }

    fn mock_interpret(&mut self) -> Value {
        let mut value_stack: SmallVec<[Value; 4]> = SmallVec::new();
        let todo = self.bootstrap();
        for node in todo.into_iter().rev() {
            let num_children = self.expr_ctx[node].num_children();
            let ret = self.expr_codegen(node, &value_stack[value_stack.len() - num_children..]);
            value_stack.truncate(value_stack.len() - num_children);
            value_stack.push(ret);
        }
        debug_assert_eq!(value_stack.len(), 1);
        value_stack[0]
    }

    /// Returns an expression todo list sorted in topo-order
    fn bootstrap(&mut self) -> Vec<ExprRef> {
        let mut todo = vec![];
        let mut nodes_to_expand = vec![self.root_expr];
        while !nodes_to_expand.is_empty() {
            for node in std::mem::take(&mut nodes_to_expand) {
                todo.push(node);
                self.expr_ctx[node].for_each_child(|c| nodes_to_expand.push(*c));
            }
        }
        todo
    }
}

trait ExprRefExt {
    /// Returns the width of bitvector if the expr might cause overflow
    fn might_overflow(&self, ctx: &expr::Context) -> Option<WidthInt>;
}

impl ExprRefExt for ExprRef {
    fn might_overflow(&self, ctx: &expr::Context) -> Option<WidthInt> {
        match ctx[*self] {
            Expr::BVAdd(.., width) | Expr::BVMul(.., width) | Expr::BVSub(.., width) => Some(width),
            _ => None,
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

    fn expr_codegen_internal(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        match &self.expr_ctx[expr] {
            Expr::BVSymbol { width, .. } => {
                assert!(
                    *width <= 64,
                    "bv with width greater than 64 is yet to implement"
                );
                let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
                let input_states_buf = self.fn_builder.block_params(self.block_id)[0];
                self.fn_builder.ins().load(
                    self.int,
                    // buffer is allocated by Rust, therefore trusted
                    ir::MemFlags::trusted(),
                    input_states_buf,
                    (param_offset * self.int.bytes()) as i32,
                )
            }
            Expr::BVLiteral(value) => {
                let value = value
                    .get(self.expr_ctx)
                    .to_i64()
                    .unwrap_or_else(|| panic!("bv with width greater than 64 is yet to implement"));
                self.fn_builder.ins().iconst(self.int, value)
            }
            // unary
            Expr::BVNot(..) => self.fn_builder.ins().bnot(args[0]),
            Expr::BVNegate(..) => self.fn_builder.ins().ineg(args[0]),
            // binary
            Expr::BVAdd(..) => self.fn_builder.ins().iadd(args[0], args[1]),
            Expr::BVSub(..) => self.fn_builder.ins().isub(args[0], args[1]),
            Expr::BVMul(..) => self.fn_builder.ins().imul(args[0], args[1]),
            Expr::BVAnd(..) => self.fn_builder.ins().band(args[0], args[1]),
            Expr::BVOr(..) => self.fn_builder.ins().bor(args[0], args[1]),
            Expr::BVXor(..) => self.fn_builder.ins().bxor(args[0], args[1]),
            Expr::BVEqual(..) => self.fn_builder.ins().icmp(IntCC::Equal, args[0], args[1]),
            Expr::BVGreater(..) => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThan, args[0], args[1])
            }
            Expr::BVGreaterSigned(..) => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, args[0], args[1])
            }
            Expr::BVGreaterEqual(..) => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThanOrEqual, args[0], args[1])
            }
            Expr::BVGreaterEqualSigned(..) => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, args[0], args[1])
            }
            Expr::BVShiftLeft(..) => self.fn_builder.ins().ishl(args[0], args[1]),
            Expr::BVShiftRight(..) => self.fn_builder.ins().ushr(args[0], args[1]),
            Expr::BVArithmeticShiftRight(..) => self.fn_builder.ins().sshr(args[0], args[1]),
            _ => todo!("{:?}", expr),
        }
    }
}
