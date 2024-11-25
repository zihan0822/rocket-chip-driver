// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{State, TransitionSystem};
use crate::expr::traversal::TraversalCmd;
use crate::expr::{
    traversal, Context, DenseExprMetaData, DenseExprMetaDataBool, ExprMetaData, ExprRef,
    ForEachChild,
};
use rustc_hash::FxHashSet;

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
    // all observable outputs are our roots
    let mut todo = sys.get_assert_assume_output_exprs();
    // ensure that all roots start with count 1
    for expr in todo.iter() {
        use_count.insert(*expr, 1);
    }

    while let Some(expr) = todo.pop() {
        if let Some(state) = states.get(&expr) {
            // for states, we also want to mark the initial and the next expression as used
            if let Some(init) = state.init {
                if !ignore_init {
                    let count = use_count[init];
                    if count == 0 {
                        use_count.insert(init, 1);
                        todo.push(init);
                    }
                }
            }
            if let Some(next) = state.next {
                let count = use_count[next];
                if count == 0 {
                    use_count.insert(next, 1);
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
    let mut visited = DenseExprMetaDataBool::default();
    let states = sys.state_map();
    let inputs = sys.input_set();

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
        if expr.is_symbol() && (states.contains_key(&expr_ref) || inputs.contains(&expr_ref)) {
            out.push(expr_ref);
        }
        visited.insert(expr_ref, true);
    }

    out
}

/// Checks whether expressions are used. This version _does not_ follow any state symbols.
fn check_expr_use(ctx: &Context, roots: &[ExprRef]) -> impl ExprMetaData<bool> {
    let mut is_used = DenseExprMetaDataBool::default();
    for &root in roots.iter() {
        traversal::top_down(ctx, root, |_, e| {
            if is_used[e] {
                TraversalCmd::Stop
            } else {
                is_used.insert(e, true);
                TraversalCmd::Continue
            }
        })
    }
    is_used
}

#[inline]
fn count_uses(
    ctx: &Context,
    expr: ExprRef,
    use_count: &mut DenseExprMetaData<UseCountInt>,
    todo: &mut Vec<ExprRef>,
) {
    ctx.get(expr).for_each_child(|child| {
        let count = use_count[*child];
        let is_first_use = count == 0;
        use_count.insert(*child, count.saturating_add(1));
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

impl Uses {
    pub fn is_used(&self) -> bool {
        self.init || self.next || self.other
    }

    pub fn new(
        e: ExprRef,
        init_used: &impl ExprMetaData<bool>,
        next_used: &impl ExprMetaData<bool>,
        other_used: &impl ExprMetaData<bool>,
    ) -> Self {
        Self {
            next: next_used[e],
            init: init_used[e],
            other: other_used[e],
        }
    }
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
    let init_exprs = sys.get_init_exprs();
    let next_exprs = sys.get_next_exprs();
    let other_exprs = if include_outputs {
        sys.get_assert_assume_output_exprs()
    } else {
        sys.get_assert_assume_exprs()
    };

    // count how often the signal is used in different situations
    let init_used = check_expr_use(ctx, &init_exprs);
    let next_used = check_expr_use(ctx, &next_exprs);
    let mut other_used = check_expr_use(ctx, &other_exprs);

    // keep track of which signals have been processed
    let mut visited = DenseExprMetaDataBool::default();
    let mut signal_order = Vec::new();

    // add all inputs
    for &input in sys.inputs.iter() {
        visited.insert(input, true);
        let uses = Uses::new(input, &init_used, &next_used, &other_used);
        signal_order.push(RootInfo { expr: input, uses });
    }

    // add all roots and give them a large other count
    let mut todo: Vec<ExprRef> =
        Vec::with_capacity(init_exprs.len() + next_exprs.len() + other_exprs.len());
    todo.extend(&init_exprs);
    todo.extend(&next_exprs);
    todo.extend(&other_exprs);
    for &expr in todo.iter() {
        other_used.insert(expr, true); // ensure that this expression will always be serialized
    }

    // visit roots in the order in which they were declared
    todo.reverse();

    // keep track of which siganls are part of the initial root set
    let is_root = FxHashSet::from_iter(todo.iter().cloned());

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
        if num_children > 0 || is_root.contains(&expr_ref) {
            let uses = Uses::new(expr_ref, &init_used, &next_used, &other_used);
            if uses.is_used() {
                signal_order.push(RootInfo {
                    expr: expr_ref,
                    uses,
                });
            }
        }
        visited.insert(expr_ref, true);
    }

    SerializeMeta { signal_order }
}

impl ForEachChild<ExprRef> for State {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        if let Some(next) = &self.next {
            visitor(next);
        }
        if let Some(init) = &self.init {
            visitor(init);
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
