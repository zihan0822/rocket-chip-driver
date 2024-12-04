// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Expr, ExprRef};

pub trait ForEachChild<T: Clone> {
    fn for_each_child(&self, visitor: impl FnMut(&T));
    fn collect_children(&self, children: &mut Vec<T>) {
        self.for_each_child(|c: &T| {
            children.push(c.clone());
        });
    }

    fn num_children(&self) -> usize;
}

impl ForEachChild<ExprRef> for Expr {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        match self {
            Expr::BVSymbol { .. } => {}  // no children
            Expr::BVLiteral { .. } => {} // no children
            Expr::BVZeroExt { e, .. } => {
                (visitor)(e);
            }
            Expr::BVSignExt { e, .. } => {
                (visitor)(e);
            }
            Expr::BVSlice { e, .. } => {
                (visitor)(e);
            }
            Expr::BVNot(e, _) => {
                (visitor)(e);
            }
            Expr::BVNegate(e, _) => {
                (visitor)(e);
            }
            Expr::BVEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVImplies(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreater(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterSigned(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterEqualSigned(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVConcat(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVAnd(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVOr(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVXor(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVShiftLeft(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVArithmeticShiftRight(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVShiftRight(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVAdd(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVMul(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedDiv(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVUnsignedDiv(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedMod(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedRem(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVUnsignedRem(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSub(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVArrayRead { array, index, .. } => {
                (visitor)(array);
                (visitor)(index);
            }
            Expr::BVIte { cond, tru, fals } => {
                (visitor)(cond);
                (visitor)(tru);
                (visitor)(fals);
            }
            Expr::ArraySymbol { .. } => {} // no children
            Expr::ArrayConstant { e, .. } => {
                (visitor)(e);
            }
            Expr::ArrayEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::ArrayStore { array, index, data } => {
                (visitor)(array);
                (visitor)(index);
                (visitor)(data)
            }
            Expr::ArrayIte { cond, tru, fals } => {
                (visitor)(cond);
                (visitor)(tru);
                (visitor)(fals);
            }
        }
    }

    fn num_children(&self) -> usize {
        match self {
            Expr::BVSymbol { .. } => 0,
            Expr::BVLiteral(_) => 0,
            Expr::BVZeroExt { .. } => 1,
            Expr::BVSignExt { .. } => 1,
            Expr::BVSlice { .. } => 1,
            Expr::BVNot(_, _) => 1,
            Expr::BVNegate(_, _) => 1,
            Expr::BVEqual(_, _) => 2,
            Expr::BVImplies(_, _) => 2,
            Expr::BVGreater(_, _) => 2,
            Expr::BVGreaterSigned(_, _, _) => 2,
            Expr::BVGreaterEqual(_, _) => 2,
            Expr::BVGreaterEqualSigned(_, _, _) => 2,
            Expr::BVConcat(_, _, _) => 2,
            Expr::BVAnd(_, _, _) => 2,
            Expr::BVOr(_, _, _) => 2,
            Expr::BVXor(_, _, _) => 2,
            Expr::BVShiftLeft(_, _, _) => 2,
            Expr::BVArithmeticShiftRight(_, _, _) => 2,
            Expr::BVShiftRight(_, _, _) => 2,
            Expr::BVAdd(_, _, _) => 2,
            Expr::BVMul(_, _, _) => 2,
            Expr::BVSignedDiv(_, _, _) => 2,
            Expr::BVUnsignedDiv(_, _, _) => 2,
            Expr::BVSignedMod(_, _, _) => 2,
            Expr::BVSignedRem(_, _, _) => 2,
            Expr::BVUnsignedRem(_, _, _) => 2,
            Expr::BVSub(_, _, _) => 2,
            Expr::BVArrayRead { .. } => 2,
            Expr::BVIte { .. } => 3,
            Expr::ArraySymbol { .. } => 0,
            Expr::ArrayConstant { .. } => 1,
            Expr::ArrayEqual(_, _) => 2,
            Expr::ArrayStore { .. } => 3,
            Expr::ArrayIte { .. } => 3,
        }
    }
}
