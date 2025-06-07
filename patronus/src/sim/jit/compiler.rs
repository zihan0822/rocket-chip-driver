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
        while let Some(next_to_expand) = nodes_to_expand.pop() {
            todo.push(next_to_expand);
            self.expr_ctx[next_to_expand].for_each_child(|&child| nodes_to_expand.push(child));
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
        if matches!(
            ctx[*self],
            Expr::BVAdd(..)
                | Expr::BVMul(..)
                | Expr::BVSub(..)
                | Expr::BVShiftLeft(..)
                | Expr::BVSignExt { .. }
                | Expr::BVNot(..)
                | Expr::BVNegate(..)
                | Expr::BVLiteral(..)
                | Expr::BVSymbol { .. }
        ) {
            self.get_type(ctx).get_bit_vector_width()
        } else {
            None
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

    fn bv_sign_extend(&mut self, value: Value, width: WidthInt) -> Value {
        let shifted = self.fn_builder.ins().ishl_imm(value, (64 - width) as i64);
        self.fn_builder.ins().sshr_imm(shifted, (64 - width) as i64)
    }

    fn expr_codegen_internal(&mut self, expr: ExprRef, args: &[Value]) -> Value {
        if !matches!(expr.get_type(&self.expr_ctx), expr::Type::BV(width) if width <= 64) {
            panic!(
                "only support bv with width less than or equal to 64, but got: `{:?}`",
                self.expr_ctx[expr]
            );
        }
        match &self.expr_ctx[expr] {
            Expr::BVSymbol { .. } => {
                let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
                let input_buffer_address = self.fn_builder.block_params(self.block_id)[0];
                self.fn_builder.ins().load(
                    self.int,
                    // buffer is allocated by Rust, therefore trusted
                    ir::MemFlags::trusted(),
                    input_buffer_address,
                    (param_offset * self.int.bytes()) as i32,
                )
            }
            Expr::BVLiteral(value) => {
                let value = value.get(self.expr_ctx).to_i64().unwrap();
                self.fn_builder.ins().iconst(self.int, value)
            }
            // unary
            Expr::BVNot(..) => self.fn_builder.ins().bnot(args[0]),
            Expr::BVNegate(..) => {
                let flipped = self.fn_builder.ins().bnot(args[0]);
                self.fn_builder.ins().iadd_imm(flipped, 1)
            }
            // no-op with current impl
            Expr::BVZeroExt { .. } => args[0],
            Expr::BVSignExt { by, width, .. } => {
                assert!(width > by);
                self.bv_sign_extend(args[0], width - by)
            }
            Expr::BVSlice { hi, lo, .. } => {
                assert!(hi >= lo);
                let shifted = self.fn_builder.ins().ushr_imm(args[0], *lo as i64);
                self.fn_builder
                    .ins()
                    .band_imm(shifted, (u64::MAX >> (64 - (*hi - *lo + 1))) as i64)
            }
            // binary
            Expr::BVAdd(..) => self.fn_builder.ins().iadd(args[0], args[1]),
            Expr::BVSub(..) => self.fn_builder.ins().isub(args[0], args[1]),
            Expr::BVMul(..) => self.fn_builder.ins().imul(args[0], args[1]),
            Expr::BVAnd(..) => self.fn_builder.ins().band(args[0], args[1]),
            Expr::BVOr(..) => self.fn_builder.ins().bor(args[0], args[1]),
            Expr::BVXor(..) => self.fn_builder.ins().bxor(args[0], args[1]),
            Expr::BVEqual(..) => {
                let cmp = self.fn_builder.ins().icmp(IntCC::Equal, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreater(..) => {
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::UnsignedGreaterThan, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterSigned(.., width) => {
                let (arg0, arg1) = (
                    self.bv_sign_extend(args[0], *width),
                    self.bv_sign_extend(args[1], *width),
                );
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, arg0, arg1);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterEqual(..) => {
                let cmp =
                    self.fn_builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, args[0], args[1]);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVGreaterEqualSigned(.., width) => {
                let (arg0, arg1) = (
                    self.bv_sign_extend(args[0], *width),
                    self.bv_sign_extend(args[1], *width),
                );
                let cmp = self
                    .fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, arg0, arg1);
                self.fn_builder.ins().uextend(self.int, cmp)
            }
            Expr::BVShiftLeft(..) => self.fn_builder.ins().ishl(args[0], args[1]),
            Expr::BVShiftRight(..) => self.fn_builder.ins().ushr(args[0], args[1]),
            Expr::BVArithmeticShiftRight(..) => self.fn_builder.ins().sshr(args[0], args[1]),
            Expr::BVIte { .. } => self.fn_builder.ins().select(args[0], args[1], args[2]),
            Expr::BVConcat(_, lo, ..) => {
                let expr::Type::BV(lo_width) = lo.get_type(self.expr_ctx) else {
                    unreachable!()
                };
                let hi = self.fn_builder.ins().ishl_imm(args[0], lo_width as i64);
                self.fn_builder.ins().bor(hi, args[1])
            }
            _ => todo!("{:?}", self.expr_ctx[expr]),
        }
    }
}
