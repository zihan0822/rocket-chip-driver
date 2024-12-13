// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, Expr, ExprRef, ForEachChild, Type, TypeCheck};
use crate::smt::solver::SmtCommand;
use baa::BitVecOps;
use std::io::Write;

pub type Result<T> = std::io::Result<T>;

pub fn serialize_expr(out: &mut impl Write, ctx: &Context, expr: ExprRef) -> Result<()> {
    // we need to visit each expression "number of children + 1" times
    let mut todo: Vec<(ExprRef, u32)> = vec![(expr, 0)];

    while let Some((e, pc)) = todo.pop() {
        let expr = &ctx[e];
        if pc == 0 {
            // first time we visit
            match expr {
                Expr::BVSymbol { name, .. } => {
                    write!(out, "{}", escape_smt_identifier(&ctx[*name]))?
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
                }
                Expr::BVZeroExt { .. } => todo!(),
                Expr::BVSignExt { .. } => todo!(),
                Expr::BVSlice { .. } => todo!(),
                Expr::BVNot(_, _) => todo!(),
                Expr::BVNegate(_, _) => todo!(),
                Expr::BVEqual(_, _) => write!(out, "(=")?,
                Expr::BVImplies(_, _) => todo!(),
                Expr::BVGreater(_, _) => todo!(),
                Expr::BVGreaterSigned(_, _, _) => todo!(),
                Expr::BVGreaterEqual(_, _) => todo!(),
                Expr::BVGreaterEqualSigned(_, _, _) => todo!(),
                Expr::BVConcat(_, _, _) => todo!(),
                Expr::BVAnd(_, _, _) => todo!(),
                Expr::BVOr(_, _, _) => todo!(),
                Expr::BVXor(_, _, _) => todo!(),
                Expr::BVShiftLeft(_, _, _) => todo!(),
                Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
                Expr::BVShiftRight(_, _, _) => todo!(),
                Expr::BVAdd(_, _, _) => todo!(),
                Expr::BVMul(_, _, _) => todo!(),
                Expr::BVSignedDiv(_, _, _) => todo!(),
                Expr::BVUnsignedDiv(_, _, _) => todo!(),
                Expr::BVSignedMod(_, _, _) => todo!(),
                Expr::BVSignedRem(_, _, _) => todo!(),
                Expr::BVUnsignedRem(_, _, _) => todo!(),
                Expr::BVSub(_, _, _) => todo!(),
                Expr::BVArrayRead { .. } => todo!(),
                Expr::BVIte { .. } => todo!(),
                Expr::ArraySymbol { .. } => todo!(),
                Expr::ArrayConstant { .. } => todo!(),
                Expr::ArrayEqual(_, _) => todo!(),
                Expr::ArrayStore { .. } => todo!(),
                Expr::ArrayIte { .. } => todo!(),
            }
        }

        if let Some(next_child) = find_next_child(pc, expr) {
            write!(out, " ")?;
            todo.push((e, pc + 1));
            todo.push((next_child, 0));
        } else if pc > 0 {
            write!(out, ")")?;
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
