// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{SignalInfo, SignalKind, TransitionSystem};
use crate::btor2::{DEFAULT_INPUT_PREFIX, DEFAULT_STATE_PREFIX};
use crate::expr::*;
use std::collections::HashMap;

/** Remove any inputs named `_input_[...]` and replace their use with a literal zero.
* This essentially gets rid of all undefined value modelling by yosys.
 */
pub fn replace_anonymous_inputs_with_zero(ctx: &mut Context, sys: &mut TransitionSystem) {
    // find and remove inputs
    let mut replace_map = HashMap::new();
    for (expr, signal_info) in sys.get_signals(|s| s.is_input()) {
        let name = ctx.get_symbol_name(expr).unwrap();
        if name.starts_with(DEFAULT_INPUT_PREFIX) || name.starts_with(DEFAULT_STATE_PREFIX) {
            let replacement = match expr.get_type(ctx) {
                Type::BV(width) => ctx.zero(width),
                Type::Array(tpe) => ctx.zero_array(tpe),
            };
            replace_map.insert(expr, replacement);
            sys.remove_signal(expr);
            // re-insert signal info if the input has labels
            if !signal_info.labels.is_none() {
                sys.add_signal(
                    replacement,
                    SignalKind::Node,
                    signal_info.labels,
                    signal_info.name,
                );
            }
        }
    }

    // replace any use of the input with zero
    do_transform(
        ctx,
        sys,
        ExprTransformMode::SingleStep,
        |_ctx, expr, _children| replace_map.get(&expr).cloned(),
    );
}

/// Applies simplifications to the expressions used in the system.
pub fn simplify_expressions(ctx: &mut Context, sys: &mut TransitionSystem) {
    do_transform(ctx, sys, ExprTransformMode::FixedPoint, simplify);
}

pub fn do_transform(
    ctx: &mut Context,
    sys: &mut TransitionSystem,
    mode: ExprTransformMode,
    tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) {
    let todo = get_root_expressions(sys);
    let mut transformed = DenseExprMetaData::default();
    do_transform_expr(ctx, mode, &mut transformed, todo, tran);

    // update transition system signals
    let signals = sys.get_signals(|_| true);
    for (old_expr, info) in signals.into_iter() {
        let new_expr = if mode == ExprTransformMode::FixedPoint {
            get_fixed_point(&mut transformed, old_expr)
        } else {
            transformed[old_expr]
        };
        if let Some(new_expr) = new_expr {
            if new_expr != old_expr {
                sys.update_signal_expr(old_expr, new_expr);
            }
        }
    }

    // update states
    for state in sys.states.iter_mut() {
        if let Some(new_symbol) = changed(&transformed, state.symbol) {
            state.symbol = new_symbol;
        }
        if let Some(old_next) = state.next {
            if let Some(new_next) = changed(&transformed, old_next) {
                state.next = Some(new_next);
            }
        }
        if let Some(old_init) = state.init {
            if let Some(new_init) = changed(&transformed, old_init) {
                state.init = Some(new_init);
            }
        }
    }
}

fn changed(transformed: &DenseExprMetaData<Option<ExprRef>>, old_expr: ExprRef) -> Option<ExprRef> {
    if let Some(new_expr) = transformed[old_expr] {
        if new_expr != old_expr {
            Some(new_expr)
        } else {
            None
        }
    } else {
        None
    }
}

fn get_root_expressions(sys: &TransitionSystem) -> Vec<ExprRef> {
    // include all input, output, assertion and assumptions expressions
    let mut out = Vec::from_iter(
        sys.get_signals(is_usage_root_signal)
            .iter()
            .map(|(e, _)| *e),
    );

    // include all states
    for (_, state) in sys.states() {
        out.push(state.symbol);
        if let Some(init) = state.init {
            out.push(init);
        }
        if let Some(next) = state.next {
            out.push(next);
        }
    }

    out
}

/// Slightly different definition from use counts, as we want to retain all inputs in transformation passes.
fn is_usage_root_signal(info: &SignalInfo) -> bool {
    info.is_input()
        || info.labels.is_output()
        || info.labels.is_constraint()
        || info.labels.is_bad()
        || info.labels.is_fair()
}
