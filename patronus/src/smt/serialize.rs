// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{traversal, Context, ExprRef, Type};
use std::io::Write;

pub type Result<T> = std::io::Result<T>;

pub fn serialize_expr(out: &mut impl Write, ctx: &Context, expr: ExprRef) -> Result<()> {
    todo!()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ArrayType;

    fn s_type(t: Type) -> String {
        let mut out = Vec::new();
        serialize_type(&mut out, t).unwrap();
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
}
