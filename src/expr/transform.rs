// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::*;
use baa::BitVecOps;

/// Applies simplifications to a single expression.
pub fn simplify_single_expression(ctx: &mut Context, expr: ExprRef) -> ExprRef {
    let todo = vec![expr];
    let res = do_transform_expr(ctx, todo, simplify);
    res.get(expr).unwrap_or(expr)
}

pub(crate) fn do_transform_expr(
    ctx: &mut Context,
    mut todo: Vec<ExprRef>,
    mut tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) -> ExprMetaData<Option<ExprRef>> {
    let mut transformed = ExprMetaData::default();
    let mut children = Vec::with_capacity(4);

    while let Some(expr_ref) = todo.pop() {
        // check to see if we translated all the children
        children.clear();
        let mut children_changed = false; // track whether any of the children changed
        let mut all_transformed = true; // tracks whether all children have been transformed or if there is more work to do
        ctx.get(expr_ref).for_each_child(|c| {
            match transformed.get(*c) {
                Some(new_child_expr) => {
                    if *new_child_expr != *c {
                        children_changed = true; // child changed
                    }
                    children.push(*new_child_expr);
                }
                None => {
                    if all_transformed {
                        todo.push(expr_ref);
                    }
                    all_transformed = false;
                    todo.push(*c);
                }
            }
        });
        if !all_transformed {
            continue;
        }

        // call out to the transform
        let tran_res = (tran)(ctx, expr_ref, &children);
        let new_expr_ref = match tran_res {
            Some(e) => e,
            None => {
                if children_changed {
                    update_expr_children(ctx, expr_ref, &children)
                } else {
                    // if no children changed and the transform does not want to do changes,
                    // we can just keep the old expression
                    expr_ref
                }
            }
        };
        // remember the transformed version
        *transformed.get_mut(expr_ref) = Some(new_expr_ref);
    }
    transformed
}

pub(crate) fn simplify(ctx: &mut Context, expr: ExprRef, children: &[ExprRef]) -> Option<ExprRef> {
    match (ctx.get(expr).clone(), children) {
        (Expr::BVIte { .. }, [cond, tru, fals]) => {
            if tru == fals {
                // condition does not matter
                Some(*tru)
            } else if let Expr::BVLiteral(value) = ctx.get(*cond) {
                if value.get(ctx).is_fals() {
                    Some(*fals)
                } else {
                    Some(*tru)
                }
            } else {
                // this unwrap should always be OK since it is a **BV**Ite
                let value_width = ctx.get(*tru).get_bv_type(ctx).unwrap();
                if value_width == 1 {
                    if let (Expr::BVLiteral(vt), Expr::BVLiteral(vf)) =
                        (ctx.get(*tru), ctx.get(*fals))
                    {
                        match (
                            vt.get(ctx).to_bool().unwrap(),
                            vf.get(ctx).to_bool().unwrap(),
                        ) {
                            (true, false) => Some(*cond),
                            (false, true) => Some(ctx.not(*cond)),
                            _ => Some(*tru),
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
        (Expr::BVAnd(_, _, 1), [a, b]) => {
            // boolean and simplifications
            if let Expr::BVLiteral(va) = ctx.get(*a) {
                if va.get(ctx).is_fals() {
                    Some(*a) /* false */
                } else {
                    Some(*b)
                }
            } else if let Expr::BVLiteral(vb) = ctx.get(*b) {
                if vb.get(ctx).is_fals() {
                    Some(*b) /* true */
                } else {
                    Some(*a)
                }
            } else {
                None
            }
        }
        (Expr::BVAnd(_, _, _), [a, b]) => {
            if let (Expr::BVLiteral(va), Expr::BVLiteral(vb)) = (ctx.get(*a), ctx.get(*b)) {
                Some(ctx.bv_lit(&va.get(ctx).and(&vb.get(ctx))))
            } else {
                None
            }
        }
        (Expr::BVOr(_, _, 1), [a, b]) => {
            // boolean or simplifications
            if let Expr::BVLiteral(va) = ctx.get(*a) {
                if va.get(ctx).is_fals() {
                    Some(*b)
                } else {
                    Some(*a) /* true */
                }
            } else if let Expr::BVLiteral(vb) = ctx.get(*b) {
                if vb.get(ctx).is_fals() {
                    Some(*a)
                } else {
                    Some(*b) /* true */
                }
            } else {
                None
            }
        }
        (Expr::BVOr(_, _, _), [a, b]) => {
            if let (Expr::BVLiteral(va), Expr::BVLiteral(vb)) = (ctx.get(*a), ctx.get(*b)) {
                Some(ctx.bv_lit(&va.get(ctx).or(&vb.get(ctx))))
            } else {
                None
            }
        }
        (Expr::BVNot(_, _), [e]) => {
            match ctx.get(*e) {
                Expr::BVNot(inner, _) => Some(*inner), // double negation
                Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).not())),
                _ => None,
            }
        }
        (Expr::BVZeroExt { by, .. }, [e]) => match ctx.get(*e) {
            Expr::BVLiteral(value) => Some(ctx.bv_lit(&value.get(ctx).zero_extend(by))),
            _ => None,
        },
        // combine slices
        (Expr::BVSlice { lo, hi, .. }, [e]) => match ctx.get(*e) {
            Expr::BVSlice {
                lo: inner_lo,
                e: inner_e,
                ..
            } => Some(ctx.slice(*inner_e, hi + inner_lo, lo + inner_lo)),
            _ => None,
        },
        _ => None, // no matching simplification
    }
}

fn update_expr_children(ctx: &mut Context, expr_ref: ExprRef, children: &[ExprRef]) -> ExprRef {
    let new_expr = match (ctx.get(expr_ref), children) {
        (Expr::BVSymbol { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVLiteral { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVZeroExt { by, width, .. }, [e]) => Expr::BVZeroExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSignExt { by, width, .. }, [e]) => Expr::BVSignExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSlice { hi, lo, .. }, [e]) => Expr::BVSlice {
            e: *e,
            hi: *hi,
            lo: *lo,
        },
        (Expr::BVNot(_, width), [e]) => Expr::BVNot(*e, *width),
        (Expr::BVNegate(_, width), [e]) => Expr::BVNegate(*e, *width),
        (Expr::BVEqual(_, _), [a, b]) => Expr::BVEqual(*a, *b),
        (Expr::BVImplies(_, _), [a, b]) => Expr::BVImplies(*a, *b),
        (Expr::BVGreater(_, _), [a, b]) => Expr::BVGreater(*a, *b),
        (Expr::BVGreaterSigned(_, _, w), [a, b]) => Expr::BVGreaterSigned(*a, *b, *w),
        (Expr::BVGreaterEqual(_, _), [a, b]) => Expr::BVGreaterEqual(*a, *b),
        (Expr::BVGreaterEqualSigned(_, _, w), [a, b]) => Expr::BVGreaterEqualSigned(*a, *b, *w),
        (Expr::BVConcat(_, _, w), [a, b]) => Expr::BVConcat(*a, *b, *w),
        (Expr::BVAnd(_, _, w), [a, b]) => Expr::BVAnd(*a, *b, *w),
        (Expr::BVOr(_, _, w), [a, b]) => Expr::BVOr(*a, *b, *w),
        (Expr::BVXor(_, _, w), [a, b]) => Expr::BVXor(*a, *b, *w),
        (Expr::BVShiftLeft(_, _, w), [a, b]) => Expr::BVShiftLeft(*a, *b, *w),
        (Expr::BVArithmeticShiftRight(_, _, w), [a, b]) => Expr::BVArithmeticShiftRight(*a, *b, *w),
        (Expr::BVShiftRight(_, _, w), [a, b]) => Expr::BVShiftRight(*a, *b, *w),
        (Expr::BVAdd(_, _, w), [a, b]) => Expr::BVAdd(*a, *b, *w),
        (Expr::BVMul(_, _, w), [a, b]) => Expr::BVMul(*a, *b, *w),
        (Expr::BVSignedDiv(_, _, w), [a, b]) => Expr::BVSignedDiv(*a, *b, *w),
        (Expr::BVUnsignedDiv(_, _, w), [a, b]) => Expr::BVUnsignedDiv(*a, *b, *w),
        (Expr::BVSignedMod(_, _, w), [a, b]) => Expr::BVSignedMod(*a, *b, *w),
        (Expr::BVSignedRem(_, _, w), [a, b]) => Expr::BVSignedRem(*a, *b, *w),
        (Expr::BVUnsignedRem(_, _, w), [a, b]) => Expr::BVUnsignedRem(*a, *b, *w),
        (Expr::BVSub(_, _, w), [a, b]) => Expr::BVSub(*a, *b, *w),
        (Expr::BVArrayRead { width, .. }, [array, index]) => Expr::BVArrayRead {
            array: *array,
            index: *index,
            width: *width,
        },
        (Expr::BVIte { .. }, [cond, tru, fals]) => Expr::BVIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (Expr::ArraySymbol { .. }, _) => panic!("No children, should never get here."),
        (
            Expr::ArrayConstant {
                index_width,
                data_width,
                ..
            },
            [e],
        ) => Expr::ArrayConstant {
            e: *e,
            index_width: *index_width,
            data_width: *data_width,
        },
        (Expr::ArrayEqual(_, _), [a, b]) => Expr::ArrayEqual(*a, *b),
        (Expr::ArrayStore { .. }, [array, index, data]) => Expr::ArrayStore {
            array: *array,
            index: *index,
            data: *data,
        },
        (Expr::ArrayIte { .. }, [cond, tru, fals]) => Expr::ArrayIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (other, _) => {
            todo!("implement code to re-create expression `{other:?}` with updated children")
        }
    };
    ctx.add_expr(new_expr)
}
