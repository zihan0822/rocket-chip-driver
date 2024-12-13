// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, Expr, ExprRef, ForEachChild, SerializableIrNode, Type, TypeCheck};
use crate::smt::solver::SmtCommand;
use baa::BitVecOps;
use std::io::Write;
use std::ptr::write;

pub type Result<T> = std::io::Result<T>;

pub fn serialize_expr(out: &mut impl Write, ctx: &Context, expr: ExprRef) -> Result<()> {
    println!("{}", expr.serialize_to_str(ctx));

    // we need to visit each expression "number of children + 1" times
    let mut todo: Vec<(ExprRef, u32, bool)> = vec![(expr, 0, false)];

    while let Some((e, pc, must_be_bit_vec)) = todo.pop() {
        let expr = &ctx[e];
        let convert_result_to_bv = e.get_bv_type(ctx) == Some(1) && must_be_bit_vec;

        let child_must_be_bit_vec: bool = if pc == 0 {
            if convert_result_to_bv {
                // 1-bit results are normally bool, we need to convert them to bit-vec
                write!(out, "(ite ")?;
            }

            // first time we visit
            match expr {
                Expr::BVSymbol { name, .. } => {
                    write!(out, "{}", escape_smt_identifier(&ctx[*name]))?;
                    false
                }
                Expr::BVLiteral(v) => {
                    let value = v.get(ctx);
                    if value.width() > 1 {
                        write!(out, "#b{}", v.get(ctx).to_bit_str())?;
                    } else if value.is_tru() {
                        write!(out, "true")?;
                    } else {
                        debug_assert!(value.is_fals());
                        write!(out, "false")?;
                    }
                    false
                }
                Expr::BVZeroExt { e, by, .. } => {
                    let width = e.get_bv_type(ctx).expect("zext only works on bv expr");
                    if width == 1 {
                        // this encoding avoids the zext by using an ite on the expanded true/false case
                        write!(out, "(ite ")?;
                    } else {
                        write!(out, "((_ zero_extend {by}) ")?;
                    }
                    // or special approach allows us to deal with booleans
                    false
                }
                Expr::BVSignExt { by, .. } => {
                    write!(out, "((_ sign_extend {by}) ")?;
                    true
                }
                Expr::BVSlice { e, hi, lo } => {
                    let width = e.get_bv_type(ctx).expect("slice only works on bv expr");
                    // skip no-op bit extracts (this helps us avoid slices on boolean values)
                    if *lo == 0 && width - 1 == *hi {
                        // nothing to do
                    } else {
                        let result_width = *hi - *lo + 1;
                        if result_width == 1 {
                            // convert to a bool
                            write!(out, "(= ((_ extract {hi} {lo}) ")?;
                        } else {
                            write!(out, "((_ extract {hi} {lo}) ")?;
                        }
                    }
                    // we can work with boolean values, since 1-bit values can only have no-op
                    // slices which we ignore
                    false
                }
                Expr::BVNot(e, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(not ")?;
                    } else {
                        write!(out, "(bvnot ")?;
                    }
                    false
                }
                Expr::BVNegate(_, _) => {
                    write!(out, "(bvneg ")?;
                    true
                }
                Expr::BVEqual(_, _) => {
                    write!(out, "(= ")?;
                    false
                }
                Expr::BVImplies(a, b) => {
                    debug_assert!(a.get_type(ctx).is_bool());
                    debug_assert!(b.get_type(ctx).is_bool());
                    write!(out, "(=> ")?;
                    false
                }
                Expr::BVGreater(_, _) => {
                    write!(out, "(bvugt ")?;
                    true
                }
                Expr::BVGreaterSigned(_, _, _) => {
                    write!(out, "(bvsgt ")?;
                    true
                }
                Expr::BVGreaterEqual(_, _) => {
                    write!(out, "(bvuge ")?;
                    true
                }
                Expr::BVGreaterEqualSigned(_, _, _) => {
                    write!(out, "(bvsge ")?;
                    true
                }
                Expr::BVConcat(_, _, _) => {
                    write!(out, "(concat ")?;
                    true
                }
                Expr::BVAnd(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(and ")?;
                    } else {
                        write!(out, "(bvand ")?;
                    }
                    false
                }
                Expr::BVOr(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(or ")?;
                    } else {
                        write!(out, "(bvor ")?;
                    }
                    false
                }
                Expr::BVXor(_, _, _) => {
                    if e.get_type(ctx).is_bool() {
                        write!(out, "(xor ")?;
                    } else {
                        write!(out, "(bvxor ")?;
                    }
                    false
                }
                Expr::BVShiftLeft(_, _, _) => {
                    write!(out, "(bvshl ")?;
                    true
                }
                Expr::BVArithmeticShiftRight(_, _, _) => {
                    write!(out, "(bvashr ")?;
                    true
                }
                Expr::BVShiftRight(_, _, _) => {
                    write!(out, "(bvlshr ")?;
                    true
                }
                Expr::BVAdd(_, _, _) => {
                    write!(out, "(bvadd ")?;
                    true
                }
                Expr::BVMul(_, _, _) => {
                    write!(out, "(bvmul ")?;
                    true
                }
                Expr::BVSignedDiv(_, _, _) => {
                    write!(out, "(bvsdiv ")?;
                    true
                }
                Expr::BVUnsignedDiv(_, _, _) => {
                    write!(out, "(bvudiv ")?;
                    true
                }
                Expr::BVSignedMod(_, _, _) => {
                    write!(out, "(bvsmod ")?;
                    true
                }
                Expr::BVSignedRem(_, _, _) => {
                    write!(out, "(bvsrem ")?;
                    true
                }
                Expr::BVUnsignedRem(_, _, _) => {
                    write!(out, "(bvurem ")?;
                    true
                }
                Expr::BVSub(_, _, _) => {
                    write!(out, "(bvsub ")?;
                    true
                }
                Expr::BVArrayRead { .. } => {
                    write!(out, "(select ")?;
                    false
                }
                Expr::BVIte { .. } => {
                    write!(out, "(ite ")?;
                    false
                }
                Expr::ArraySymbol { name, .. } => {
                    write!(out, "{}", escape_smt_identifier(&ctx[*name]))?;
                    false
                }
                Expr::ArrayConstant { .. } => {
                    write!(out, "((as const ")?;
                    let tpe = expr.get_type(ctx);
                    serialize_type(out, tpe)?;
                    write!(out, ") ")?;
                    false
                }
                Expr::ArrayEqual(_, _) => {
                    write!(out, "(= ")?;
                    false
                }
                Expr::ArrayStore { .. } => {
                    write!(out, "(store ")?;
                    false
                }
                Expr::ArrayIte { .. } => {
                    write!(out, "(ite ")?;
                    false
                }
            }
        } else {
            matches!(
                expr,
                // expressions that require their 2nd+ children to be a bitvector
                // note: result should not matter for expressions with 0 or 1 child
                Expr::BVGreater(_, _)
                    | Expr::BVGreaterSigned(_, _, _)
                    | Expr::BVGreaterEqual(_, _)
                    | Expr::BVGreaterEqualSigned(_, _, _)
                    | Expr::BVConcat(_, _, _)
                    | Expr::BVShiftLeft(_, _, _)
                    | Expr::BVArithmeticShiftRight(_, _, _)
                    | Expr::BVShiftRight(_, _, _)
                    | Expr::BVAdd(_, _, _)
                    | Expr::BVMul(_, _, _)
                    | Expr::BVSignedDiv(_, _, _)
                    | Expr::BVUnsignedDiv(_, _, _)
                    | Expr::BVSignedMod(_, _, _)
                    | Expr::BVSignedRem(_, _, _)
                    | Expr::BVUnsignedRem(_, _, _)
                    | Expr::BVSub(_, _, _)
            )
        };

        if let Some(next_child) = find_next_child(pc, expr) {
            write!(out, " ")?;
            todo.push((e, pc + 1, must_be_bit_vec));
            todo.push((next_child, 0, child_must_be_bit_vec));
        } else {
            // we had to serialize some children first => we need a closing parenthesis
            if pc > 0 {
                // special continuation for zero extend of booleans (for which we use an ite)
                if let Expr::BVZeroExt { e, by, .. } = expr {
                    if e.get_type(ctx).is_bool() {
                        let zeros = "0".repeat(*by as usize);
                        write!(out, " #b{}1 #b{}0", zeros, zeros)?;
                    }
                }
                // everyone gets a closing parenthesis
                write!(out, ")")?;
                // special continuation for slice with a 1-bit result
                if let Expr::BVSlice { hi, lo, .. } = expr {
                    if hi == lo {
                        // slice(...) == 1?
                        write!(out, " #b1)")?;
                    }
                }
            }
            if convert_result_to_bv {
                // 1-bit results are normally bool, we need to convert them to bit-vec
                write!(out, " #b1 #b0)")?;
            }
        }
    }
    Ok(())
}

fn find_next_child(pos: u32, e: &Expr) -> Option<ExprRef> {
    let mut count = 0;
    let mut out = None;
    e.for_each_child(|c| {
        if count == pos {
            out = Some(*c);
        }
        count += 1;
    });
    out
}

pub fn serialize_cmd(out: &mut impl Write, ctx: Option<&Context>, cmd: &SmtCommand) -> Result<()> {
    match cmd {
        SmtCommand::Exit => writeln!(out, "(exit)"),
        SmtCommand::CheckSat => writeln!(out, "(check-sat)"),
        SmtCommand::SetLogic(logic) => writeln!(out, "(set-logic {})", logic.to_smt_str()),
        SmtCommand::SetOption(name, value) => writeln!(out, "(set-option :{name} {value})"),
        SmtCommand::Assert(e) => {
            write!(out, "(assert ")?;
            serialize_expr(out, ctx.unwrap(), *e)?;
            writeln!(out, ")")
        }
        SmtCommand::DeclareConst(symbol) => {
            let ctx = ctx.unwrap();
            write!(
                out,
                "(declare-const {} ",
                ctx.get_symbol_name(*symbol).unwrap()
            )?;
            serialize_type(out, symbol.get_type(ctx))?;
            writeln!(out, ")")
        }
        SmtCommand::DefineConst(symbol, value) => {
            let ctx = ctx.unwrap();
            // name, then empty arguments
            write!(
                out,
                "(define-fun {} () ",
                ctx.get_symbol_name(*symbol).unwrap()
            )?;
            serialize_type(out, symbol.get_type(ctx))?;
            write!(out, " ")?;
            serialize_expr(out, ctx, *value)?;
            writeln!(out, ")")
        }
        SmtCommand::CheckSatAssuming(exprs) => {
            let ctx = ctx.unwrap();
            write!(out, "(check-sat-assuming (")?;
            for &e in exprs.iter() {
                serialize_expr(out, ctx, e)?;
                write!(out, " ")?;
            }
            writeln!(out, "))")
        }
        SmtCommand::Push(n) => writeln!(out, "(push {n})"),
        SmtCommand::Pop(n) => writeln!(out, "(pop {n})"),
        SmtCommand::GetValue(e) => {
            let ctx = ctx.unwrap();
            write!(out, "(get-value (")?;
            serialize_expr(out, ctx, *e)?;
            writeln!(out, "))")
        }
    }
}

pub fn serialize_type(out: &mut impl Write, tpe: Type) -> Result<()> {
    match tpe {
        Type::BV(1) => write!(out, "Bool"),
        Type::BV(width) => write!(out, "(_ BitVec {width})"),
        Type::Array(a) => match (a.index_width, a.data_width) {
            (1, 1) => write!(out, "(Array Bool Bool)"),
            (1, d) => write!(out, "(Array Bool (_ BitVec {d}))"),
            (i, 1) => write!(out, "(Array (_ BitVec {i}) Bool)"),
            (i, d) => write!(out, "(Array (_ BitVec {i}) (_ BitVec {d}))"),
        },
    }
}

/// See <simple_symbol> definition in the Concrete Syntax Appendix of the SMTLib Spec
fn is_simple_smt_identifier(id: &str) -> bool {
    if id.is_empty() {
        return false; // needs to be non-empty
    }
    let mut is_first = true;
    for cc in id.chars() {
        if !cc.is_ascii() {
            return false; // all allowed characters are ASCII characters
        }
        let ac = cc as u8;
        let is_alpha = ac.is_ascii_uppercase() || ac.is_ascii_lowercase();
        let is_num = ac.is_ascii_digit();
        let is_other_allowed_char = matches!(
            ac,
            b'+' | b'-'
                | b'/'
                | b'*'
                | b'='
                | b'%'
                | b'?'
                | b'!'
                | b'.'
                | b'$'
                | b'_'
                | b'~'
                | b'&'
                | b'^'
                | b'<'
                | b'>'
                | b'@'
        );
        if !(is_alpha | is_num | is_other_allowed_char) {
            return false;
        }
        if is_num && is_first {
            return false; // the first character is not allowed ot be a digit
        }
        is_first = false;
    }
    true // passed all checks
}

fn escape_smt_identifier(id: &str) -> std::borrow::Cow<'_, str> {
    if is_simple_smt_identifier(id) {
        std::borrow::Cow::Borrowed(id)
    } else {
        let escaped = format!("|{}|", id);
        std::borrow::Cow::Owned(escaped)
    }
}

#[cfg(test)]
fn unescape_smt_identifier(id: &str) -> &str {
    if id.starts_with("|") {
        assert!(id.ends_with("|"));
        &id[1..id.len() - 1]
    } else {
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ArrayType;

    #[test]
    fn test_our_escaping() {
        assert_eq!(
            unescape_smt_identifier(&escape_smt_identifier("a b")),
            "a b"
        );
    }

    fn s_type(t: Type) -> String {
        let mut out = Vec::new();
        serialize_type(&mut out, t).unwrap();
        String::from_utf8(out).unwrap()
    }

    fn s_expr(ctx: &Context, e: ExprRef) -> String {
        let mut out = Vec::new();
        serialize_expr(&mut out, ctx, e).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn test_serialize_types() {
        assert_eq!(s_type(Type::BV(1)), "Bool");
        assert_eq!(s_type(Type::BV(2)), "(_ BitVec 2)");
        assert_eq!(s_type(Type::BV(123)), "(_ BitVec 123)");
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 3,
                data_width: 5,
            })),
            "(Array (_ BitVec 3) (_ BitVec 5))"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 1,
                data_width: 5,
            })),
            "(Array Bool (_ BitVec 5))"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 3,
                data_width: 1,
            })),
            "(Array (_ BitVec 3) Bool)"
        );
        assert_eq!(
            s_type(Type::Array(ArrayType {
                index_width: 1,
                data_width: 1,
            })),
            "(Array Bool Bool)"
        );
    }

    #[test]
    fn test_serialize_nullary_expr() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 2);
        assert_eq!(s_expr(&ctx, a), "a");
        assert_eq!(s_expr(&ctx, ctx.fals()), "false");
        assert_eq!(s_expr(&ctx, ctx.tru()), "true");
        let bv_lit = ctx.bit_vec_val(3, 3);
        assert_eq!(s_expr(&ctx, bv_lit), "#b011");
    }
}
