// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{Context, Expr, ExprMetaData, ExprRef, TypeCheck};
use baa::BitVecOps;

/// Performs simplification and canonicalization on expressions and caches the results.
pub struct Simplifier<T: ExprMetaData<Option<ExprRef>>> {
    cache: T,
}

impl<T: ExprMetaData<Option<ExprRef>>> Simplifier<T> {
    pub fn new(cache: T) -> Self {
        Self { cache }
    }

    pub fn simplify(&mut self, ctx: &mut Context, e: ExprRef) -> ExprRef {
        todo!()
    }
}

fn simplify_ite(ctx: &mut Context, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
    // ite(_, a, a) -> a
    if tru == fals {
        return tru;
    }

    // constant condition
    if let Expr::BVLiteral(value) = ctx.get(cond) {
        if value.get(ctx).is_fals() {
            // ite(false, a, b) -> b
            return fals;
        } else {
            // ite(true,  a, b) -> a
            return tru;
        }
    }

    // boolean return type
    let value_width = ctx.get(tru).get_bv_type(ctx).unwrap();
    debug_assert_eq!(
        ctx.get(fals).get_bv_type(ctx),
        ctx.get(tru).get_bv_type(ctx)
    );
    if value_width == 1 {
        if let (Expr::BVLiteral(vt), Expr::BVLiteral(vf)) = (ctx.get(tru), ctx.get(fals)) {
            let res = match (
                vt.get(ctx).to_bool().unwrap(),
                vf.get(ctx).to_bool().unwrap(),
            ) {
                // ite(cond, true, false) -> cond
                (true, false) => cond,
                // ite(cond, false, true) -> !cond
                (false, true) => ctx.not(cond),
                _ => unreachable!(
                    "both arguments are the same, this should have been handled earlier"
                ),
            };
            return res;
        }
    }

    // no transform, reconstruct ite
    ctx.bv_ite(cond, tru, fals)
}
