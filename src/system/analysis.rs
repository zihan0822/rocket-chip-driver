// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{SignalInfo, SignalKind, State, TransitionSystem};
use crate::expr::{Context, DenseExprMetaData, ExprRef, ForEachChild};

pub type UseCountInt = u16;

pub fn count_expr_uses(ctx: &Context, sys: &TransitionSystem) -> Vec<UseCountInt> {
    internal_count_expr_uses(ctx, sys, false)
}

fn internal_count_expr_uses(
    ctx: &Context,
    sys: &TransitionSystem,
    ignore_init: bool,
) -> Vec<UseCountInt> {
    let mut use_count: DenseExprMetaData<UseCountInt> = DenseExprMetaData::default();
    let states = sys.state_map();
    let mut todo = Vec::from_iter(
        sys.get_signals(is_usage_root_signal)
            .iter()
            .map(|(e, _)| *e),
    );
    // ensure that all roots start with count 1
    for expr in todo.iter() {
        use_count[*expr] = 1;
    }

    while let Some(expr) = todo.pop() {
        if let Some(state) = states.get(&expr) {
            // for states, we also want to mark the initial and the next expression as used
            if let Some(init) = state.init {
                if !ignore_init {
                    let count = &mut use_count[init];
                    if *count == 0 {
                        *count = 1;
                        todo.push(init);
                    }
                }
            }
            if let Some(next) = state.next {
                let count = &mut use_count[next];
                if *count == 0 {
                    *count = 1;
                    todo.push(next);
                }
            }
        }

        count_uses(ctx, expr, &mut use_count, &mut todo);
    }

    use_count.into_vec()
}

/// Generates a list of all inputs and states that can influence the `root` expression.
pub fn cone_of_influence(ctx: &Context, sys: &TransitionSystem, root: ExprRef) -> Vec<ExprRef> {
    // we need to follow next and init expressions for all states
    cone_of_influence_impl(ctx, sys, root, true, true)
}

/// Generates a list of all inputs and states that can influence the `root` expression, while the system is being initialized.
pub fn cone_of_influence_init(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
) -> Vec<ExprRef> {
    cone_of_influence_impl(ctx, sys, root, false, true)
}

/// Generates a list of all inputs and states that can influence the `root` expression, combinationally.
pub fn cone_of_influence_comb(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
) -> Vec<ExprRef> {
    cone_of_influence_impl(ctx, sys, root, false, false)
}

/// Internal implementation which allows us to define how we follow states.
fn cone_of_influence_impl(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
    follow_next: bool,
    follow_init: bool,
) -> Vec<ExprRef> {
    let mut out = vec![];
    let mut todo = vec![root];
    let mut visited = DenseExprMetaData::default();
    let states = sys.state_map();

    while let Some(expr_ref) = todo.pop() {
        if visited[expr_ref] {
            continue;
        }

        // make sure children are visited
        let expr = ctx.get(expr_ref);
        expr.for_each_child(|c| {
            if !visited[*c] {
                todo.push(*c);
            }
        });

        // for states, we might want to follow the next and init expressions
        if let Some(state) = states.get(&expr_ref) {
            if follow_init {
                if let Some(c) = state.init {
                    if !visited[c] {
                        todo.push(c);
                    }
                }
            }
            if follow_next {
                if let Some(c) = state.next {
                    if !visited[c] {
                        todo.push(c);
                    }
                }
            }
        }

        // check to see if this is a state or input
        if expr.is_symbol() {
            let is_state_or_input = sys
                .get_signal(expr_ref)
                .map(|i| i.is_input() || i.is_state())
                .unwrap_or(false);
            if is_state_or_input {
                out.push(expr_ref);
            }
        }
        visited[expr_ref] = true;
    }

    out
}

/// Returns whether a signal is always "used", i.e. visible to the outside world or not.
pub fn is_usage_root_signal(info: &SignalInfo) -> bool {
    info.labels.is_output()
        || info.labels.is_constraint()
        || info.labels.is_bad()
        || info.labels.is_fair()
}

pub fn is_non_output_root_signal(info: &SignalInfo) -> bool {
    info.labels.is_constraint() || info.labels.is_bad() || info.labels.is_fair()
}

/// Counts how often expressions are used. This version _does not_ follow any state symbols.
fn simple_count_expr_uses(ctx: &Context, roots: Vec<ExprRef>) -> Vec<UseCountInt> {
    let mut use_count = DenseExprMetaData::default();
    let mut todo = roots;

    // ensure that all roots start with count 1
    for expr in todo.iter() {
        use_count[*expr] = 1;
    }

    while let Some(expr) = todo.pop() {
        count_uses(ctx, expr, &mut use_count, &mut todo);
    }

    use_count.into_vec()
}

#[inline]
fn count_uses(
    ctx: &Context,
    expr: ExprRef,
    use_count: &mut DenseExprMetaData<UseCountInt>,
    todo: &mut Vec<ExprRef>,
) {
    ctx.get(expr).for_each_child(|child| {
        let count = &mut use_count[*child];
        let is_first_use = *count == 0;
        *count += 1;
        if is_first_use {
            todo.push(*child);
        }
    });
}

#[derive(Debug, Clone)]
pub struct RootInfo {
    pub expr: ExprRef,
    pub uses: Uses,
}

/// Indicates which context an expression is used in.
#[derive(Debug, Clone, Default)]
pub struct Uses {
    pub next: bool,
    pub init: bool,
    pub other: bool,
}

/// Meta-data that helps with serialization, no matter if serializing to btor, our custom
/// "human-readable" format or SMTLib.
#[derive(Debug, Default, Clone)]
pub struct SerializeMeta {
    pub signal_order: Vec<RootInfo>,
}

pub fn analyze_for_serialization(
    ctx: &Context,
    sys: &TransitionSystem,
    include_outputs: bool,
) -> SerializeMeta {
    // first we identify which expressions are used for init and which are used for next
    let (init_count, next_count, mut other_count) = init_counts(ctx, sys, include_outputs);

    let mut visited = DenseExprMetaData::default();
    let mut signal_order = Vec::new();

    // add all inputs
    for (input, _) in sys.get_signals(|s| s.kind == SignalKind::Input) {
        visited[input] = true;
        let (uses, _) = analyze_use(input, &init_count, &next_count, &other_count);
        signal_order.push(RootInfo { expr: input, uses });
    }

    // add all roots to todo list
    let mut todo = Vec::new();
    let filter = if include_outputs {
        is_usage_root_signal
    } else {
        is_non_output_root_signal
    };
    for (expr, _) in sys.get_signals(filter) {
        todo.push(expr);
        other_count[expr.index()] = 100; // ensure that this expression will always be serialized
    }
    for (_, state) in sys.states() {
        if let Some(expr) = state.next {
            todo.push(expr);
        }
        if let Some(expr) = state.init {
            todo.push(expr);
        }
    }

    // visit roots in the order in which they were declared
    todo.reverse();

    // visit expressions
    while let Some(expr_ref) = todo.pop() {
        if visited[expr_ref] {
            continue;
        }

        let expr = ctx.get(expr_ref);

        // check to see if all children are done
        let mut all_done = true;
        let mut num_children = 0;
        expr.for_each_child(|c| {
            if !visited[*c] {
                if all_done {
                    todo.push(expr_ref); // return expression to the todo list
                }
                all_done = false;
                // we need to visit the child first
                todo.push(*c);
            }
            num_children += 1;
        });

        if !all_done {
            continue;
        }

        // add to signal order if applicable
        if num_children > 0
            || sys
                .get_signal(expr_ref)
                .map(|i| !i.labels.is_none())
                .unwrap_or(false)
        {
            let (uses, total_use) = analyze_use(expr_ref, &init_count, &next_count, &other_count);
            if total_use > 1 {
                signal_order.push(RootInfo {
                    expr: expr_ref,
                    uses,
                });
            }
        }
        visited[expr_ref] = true;
    }

    SerializeMeta { signal_order }
}

fn analyze_use(
    expr_ref: ExprRef,
    init_count: &[UseCountInt],
    next_count: &[UseCountInt],
    other_count: &[UseCountInt],
) -> (Uses, UseCountInt) {
    let ii = expr_ref.index();
    let init = *init_count.get(ii).unwrap_or(&0);
    let next = *next_count.get(ii).unwrap_or(&0);
    let other = *other_count.get(ii).unwrap_or(&0);
    let total = init + next + other;
    (
        Uses {
            init: init > 0,
            next: next > 0,
            other: other > 0,
        },
        total,
    )
}

fn init_counts(
    ctx: &Context,
    sys: &TransitionSystem,
    include_outputs: bool,
) -> (Vec<UseCountInt>, Vec<UseCountInt>, Vec<UseCountInt>) {
    let mut init_roots = Vec::new();
    let mut next_roots = Vec::new();
    for (_, state) in sys.states() {
        if let Some(next) = state.next {
            next_roots.push(next);
        }
        if let Some(init) = state.init {
            init_roots.push(init);
        }
    }

    let filter = if include_outputs {
        is_usage_root_signal
    } else {
        is_non_output_root_signal
    };
    let other_roots = Vec::from_iter(sys.get_signals(filter).iter().map(|(e, _)| *e));

    let init_count = simple_count_expr_uses(ctx, init_roots);
    let next_count = simple_count_expr_uses(ctx, next_roots);
    let other_count = simple_count_expr_uses(ctx, other_roots);

    (init_count, next_count, other_count)
}

impl ForEachChild<ExprRef> for State {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        if let Some(next) = &self.next {
            (visitor)(next);
        }
        if let Some(init) = &self.init {
            (visitor)(init);
        }
    }

    fn num_children(&self) -> usize {
        self.next.is_some() as usize + self.init.is_some() as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btor2;

    fn format_symbol_list(ctx: &Context, symbols: &[ExprRef]) -> String {
        let v: Vec<_> = symbols
            .iter()
            .map(|s| ctx.get_symbol_name(*s).unwrap())
            .collect();
        v.join(", ")
    }

    #[test]
    fn test_cone_of_influence() {
        let (ctx, sys) = btor2::parse_file("inputs/unittest/delay.btor").unwrap();
        let reg0 = sys.get_state_by_name(&ctx, "reg0").unwrap().symbol;
        let reg1 = sys.get_state_by_name(&ctx, "reg1").unwrap().symbol;
        let cone0 = cone_of_influence(&ctx, &sys, reg0);
        let cone1 = cone_of_influence(&ctx, &sys, reg1);
        insta::assert_snapshot!(format_symbol_list(&ctx, &cone0));
        insta::assert_snapshot!(format_symbol_list(&ctx, &cone1));
        let cone2 = cone_of_influence_init(&ctx, &sys, reg0);
        assert_eq!(cone2, [reg0], "reg0 is initialized to zero. {:?}", cone2);
        let cone3 = cone_of_influence_init(&ctx, &sys, reg1);
        assert_eq!(cone3, [reg1], "reg1 is initialized to zero. {:?}", cone3);
    }
}
