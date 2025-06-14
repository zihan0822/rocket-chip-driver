#![allow(dead_code)]
#![allow(unused_variables)]

use crate::expr::{self, *};
use baa::{BitVecOps, BitVecValue, BitVecValueRef};
use cranelift::codegen::ir::FuncRef;
use cranelift::prelude::*;

use super::compiler::{BVCodeGenVTable, CodeGenContext};

pub(super) struct BVWord(pub(super) WidthInt);
pub(super) struct BVIndirect(pub(super) WidthInt);

impl BVWord {
    fn sign_extend_to_word(
        &self,
        value: Value,
        width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        let shifted = ctx.fn_builder.ins().ishl_imm(value, (64 - width) as i64);
        ctx.fn_builder.ins().sshr_imm(shifted, (64 - width) as i64)
    }

    fn overflow_guard(&self, value: Value, ctx: &mut CodeGenContext) -> Value {
        self.mask(value, self.0, ctx)
    }

    fn mask(&self, value: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width < 64 {
            ctx.fn_builder
                .ins()
                .band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
        } else {
            value
        }
    }

    fn cmp(&self, lhs: Value, rhs: Value, condcode: IntCC, ctx: &mut CodeGenContext) -> Value {
        let cmp = ctx.fn_builder.ins().icmp(condcode, lhs, rhs);
        ctx.fn_builder.ins().uextend(ctx.int, cmp)
    }
}

impl BVCodeGenVTable for BVWord {
    fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        ctx.load_input_state(arg)
    }

    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder
            .ins()
            .iconst(ctx.int, value.to_u64().unwrap() as i64)
    }

    fn add(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().iadd(lhs, rhs), ctx)
    }
    fn sub(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().isub(lhs, rhs), ctx)
    }
    fn mul(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().imul(lhs, rhs), ctx)
    }

    fn and(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().band(lhs, rhs)
    }
    fn or(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bor(lhs, rhs)
    }
    fn xor(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bxor(lhs, rhs)
    }

    fn not(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().bnot(arg), ctx)
    }
    fn negate(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        let flipped = ctx.fn_builder.ins().bnot(arg);
        self.overflow_guard(ctx.fn_builder.ins().iadd_imm(flipped, 1), ctx)
    }
    fn zero_extend(&self, arg: Value, _by: WidthInt, _ctx: &mut CodeGenContext) -> Value {
        arg
    }
    fn sign_extend(&self, arg: Value, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(self.sign_extend_to_word(arg, self.0 - by, ctx), ctx)
    }

    fn shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().ushr(arg0, arg1)
    }
    fn arithmetic_shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().sshr(arg0, arg1)
    }
    fn shift_left(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().ishl(arg0, arg1), ctx)
    }

    fn equal(&self, lhs: Value, rhs: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width <= 64 {
            self.cmp(lhs, rhs, IntCC::Equal, ctx)
        } else {
            invoke_bv_extern_function(ctx.runtime_lib.bv_ops["equal"], &[lhs, rhs], ctx, self.0)
        }
    }
    fn gt(&self, lhs: Value, rhs: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width <= 64 {
            self.cmp(lhs, rhs, IntCC::UnsignedGreaterThan, ctx)
        } else {
            invoke_bv_extern_function(ctx.runtime_lib.bv_ops["gt"], &[lhs, rhs], ctx, self.0)
        }
    }
    fn ge(&self, lhs: Value, rhs: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width <= 64 {
            self.cmp(lhs, rhs, IntCC::UnsignedGreaterThanOrEqual, ctx)
        } else {
            invoke_bv_extern_function(ctx.runtime_lib.bv_ops["ge"], &[lhs, rhs], ctx, self.0)
        }
    }
    fn gt_signed(
        &self,
        lhs: Value,
        rhs: Value,
        width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        if width <= 64 {
            self.cmp(lhs, rhs, IntCC::SignedGreaterThan, ctx)
        } else {
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["gt_signed"],
                &[lhs, rhs],
                ctx,
                self.0,
            )
        }
    }
    fn ge_signed(
        &self,
        lhs: Value,
        rhs: Value,
        width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        if width <= 64 {
            self.cmp(lhs, rhs, IntCC::SignedGreaterThanOrEqual, ctx)
        } else {
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["ge_signed"],
                &[lhs, rhs],
                ctx,
                self.0,
            )
        }
    }

    fn concat(
        &self,
        hi: Value,
        lo: Value,
        _hi_width: WidthInt,
        lo_width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        let hi = ctx.fn_builder.ins().ishl_imm(hi, lo_width as i64);
        ctx.fn_builder.ins().bor(hi, lo)
    }

    fn slice(
        &self,
        value: Value,
        original_width: WidthInt,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        if original_width <= 64 {
            let shifted = ctx.fn_builder.ins().ushr_imm(value, lo as i64);
            self.mask(shifted, hi - lo + 1, ctx)
        } else {
            let hi = ctx.fn_builder.ins().iconst(ctx.int, hi as i64);
            let lo = ctx.fn_builder.ins().iconst(ctx.int, lo as i64);
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["slice"],
                &[value, hi, lo],
                ctx,
                self.0,
            )
        }
    }
}

fn invoke_bv_extern_function(
    func: FuncRef,
    args: &[Value],
    ctx: &mut CodeGenContext,
    ret_width: WidthInt,
) -> Value {
    let call = ctx.fn_builder.ins().call(func, args);
    let ret = ctx.fn_builder.inst_results(call)[0];
    if ret_width > 64 {
        ctx.register_heap_allocation(ret, expr::Type::BV(ret_width));
    }
    ret
}

impl BVCodeGenVTable for BVIndirect {
    fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        let value = ctx.load_input_state(arg);
        ctx.clone_bv(value, self.0)
    }

    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        let owned_bv_literal: Box<BitVecValue> = Box::new(value.into());
        let ptr = owned_bv_literal.as_ref() as *const BitVecValue;
        ctx.bv_data.push(owned_bv_literal);
        let src = ctx.fn_builder.ins().iconst(ctx.int, ptr as i64);
        ctx.clone_bv(src, self.0)
    }

    fn add(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["add"], &[lhs, rhs], ctx, self.0)
    }
    fn sub(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["sub"], &[lhs, rhs], ctx, self.0)
    }
    fn mul(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["mul"], &[lhs, rhs], ctx, self.0)
    }
    fn and(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["and"], &[lhs, rhs], ctx, self.0)
    }
    fn or(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["or"], &[lhs, rhs], ctx, self.0)
    }
    fn xor(&self, lhs: Value, rhs: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["xor"], &[lhs, rhs], ctx, self.0)
    }
    fn not(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["not"], &[arg], ctx, self.0)
    }
    fn negate(&self, arg: Value, ctx: &mut CodeGenContext) -> Value {
        invoke_bv_extern_function(ctx.runtime_lib.bv_ops["negate"], &[arg], ctx, self.0)
    }

    fn zero_extend(&self, arg: Value, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let original_width = ctx.fn_builder.ins().iconst(ctx.int, (self.0 - by) as i64);
        let by = ctx.fn_builder.ins().iconst(ctx.int, by as i64);
        invoke_bv_extern_function(
            ctx.runtime_lib.bv_ops["zero_extend"],
            &[arg, original_width, by],
            ctx,
            self.0,
        )
    }
    fn sign_extend(&self, arg: Value, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let original_width = ctx.fn_builder.ins().iconst(ctx.int, (self.0 - by) as i64);
        let by = ctx.fn_builder.ins().iconst(ctx.int, by as i64);
        invoke_bv_extern_function(
            ctx.runtime_lib.bv_ops["sign_extend"],
            &[arg, original_width, by],
            ctx,
            self.0,
        )
    }

    fn shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        todo!()
    }
    fn arithmetic_shift_right(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        todo!()
    }
    fn shift_left(&self, arg0: Value, arg1: Value, ctx: &mut CodeGenContext) -> Value {
        todo!()
    }
    fn equal(
        &self,
        _lhs: Value,
        _rhs: Value,
        _width: WidthInt,
        _ctx: &mut CodeGenContext,
    ) -> Value {
        unreachable!()
    }
    fn gt(&self, _lhs: Value, _rhs: Value, _width: WidthInt, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn ge(&self, _lhs: Value, _rhs: Value, _width: WidthInt, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn gt_signed(
        &self,
        _lhs: Value,
        _rhs: Value,
        _width: WidthInt,
        _ctx: &mut CodeGenContext,
    ) -> Value {
        unreachable!()
    }
    fn ge_signed(
        &self,
        _lhs: Value,
        _rhs: Value,
        _width: WidthInt,
        _ctx: &mut CodeGenContext,
    ) -> Value {
        unreachable!()
    }
    fn concat(
        &self,
        hi: Value,
        lo: Value,
        hi_width: WidthInt,
        lo_width: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        let hi_width = ctx.fn_builder.ins().iconst(ctx.int, hi_width as i64);
        let lo_width = ctx.fn_builder.ins().iconst(ctx.int, lo_width as i64);
        invoke_bv_extern_function(
            ctx.runtime_lib.bv_ops["concat"],
            &[hi, lo, hi_width, lo_width],
            ctx,
            self.0,
        )
    }
    fn slice(
        &self,
        value: Value,
        _original_width: WidthInt,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        let hi = ctx.fn_builder.ins().iconst(ctx.int, hi as i64);
        let lo = ctx.fn_builder.ins().iconst(ctx.int, lo as i64);
        invoke_bv_extern_function(
            ctx.runtime_lib.bv_ops["slice"],
            &[value, hi, lo],
            ctx,
            self.0,
        )
    }
}
