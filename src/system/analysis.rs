// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{State, TransitionSystem};
use crate::expr::traversal::TraversalCmd;
use crate::expr::{
    traversal, Context, DenseExprMetaData, DenseExprSet, ExprRef, ExprSet, ForEachChild,
};

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
        use_count[*expr] = 1;
    }

    while let Some(expr) = todo.pop() {
        if let Some(state) = states.get(&expr) {
            // for states, we also want to mark the initial and the next expression as used
            if let Some(init) = state.init {
                if !ignore_init {
                    let count = use_count[init];
                    if count == 0 {
                        use_count[init] = 1;
                        todo.push(init);
                    }
                }
            }
            if let Some(next) = state.next {
                let count = use_count[next];
                if count == 0 {
                    use_count[next] = 1;
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
    let mut visited = DenseExprSet::default();
    let states = sys.state_map();
    let inputs = sys.input_set();

    while let Some(expr_ref) = todo.pop() {
        if visited.contains(&expr_ref) {
            continue;
        }

        // make sure children are visited
        let expr = ctx.get(expr_ref);
        expr.for_each_child(|c| {
            if !visited.contains(c) {
                todo.push(*c);
            }
        });

        // for states, we might want to follow the next and init expressions
        if let Some(state) = states.get(&expr_ref) {
            if follow_init {
                if let Some(c) = state.init {
                    if !visited.contains(&c) {
                        todo.push(c);
                    }
                }
            }
            if follow_next {
                if let Some(c) = state.next {
                    if !visited.contains(&c) {
                        todo.push(c);
                    }
                }
            }
        }

        // check to see if this is a state or input
        if expr.is_symbol() && (states.contains_key(&expr_ref) || inputs.contains(&expr_ref)) {
            out.push(expr_ref);
        }
        visited.insert(expr_ref);
    }

    out
}

/// Checks whether expressions are used. This version _does not_ follow any state symbols.
fn check_expr_use(ctx: &Context, roots: &[ExprRef]) -> impl ExprSet {
    let mut is_used = DenseExprSet::default();
    for &root in roots.iter() {
        traversal::top_down(ctx, root, |_, e| {
            if is_used.contains(&e) {
                TraversalCmd::Stop
            } else {
                is_used.insert(e);
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
        use_count[*child] = count.saturating_add(1);
        if is_first_use {
            todo.push(*child);
        }
    });
}

#[derive(Debug, Clone)]
pub struct RootInfo {
    pub expr: ExprRef,
    pub uses: Uses,
    pub kind: SerializeSignalKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SerializeSignalKind {
    BadState,
    Constraint,
    Output,
    Input,
    StateInit,
    StateNext,
    None,
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
        init_used: &impl ExprSet,
        next_used: &impl ExprSet,
        other_used: &impl ExprSet,
    ) -> Self {
        Self {
            next: next_used.contains(&e),
            init: init_used.contains(&e),
            other: other_used.contains(&e),
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

    // always add all inputs to the signal order
    let mut signal_order = Vec::new();
    for &input in sys.inputs.iter() {
        let uses = Uses::new(input, &init_used, &next_used, &other_used);
        signal_order.push(RootInfo {
            expr: input,
            uses,
            kind: SerializeSignalKind::Input,
        });
    }

    // keep track of which signals have been processed
    let mut visited = DenseExprSet::default();

    // add all roots and give them a large other count
    let mut todo: Vec<(ExprRef, SerializeSignalKind)> =
        Vec::with_capacity(init_exprs.len() + next_exprs.len() + other_exprs.len());
    todo.extend(
        sys.constraints
            .iter()
            .map(|&e| (e, SerializeSignalKind::Constraint)),
    );
    todo.extend(
        sys.bad_states
            .iter()
            .map(|&e| (e, SerializeSignalKind::BadState)),
    );
    if include_outputs {
        todo.extend(
            sys.outputs
                .iter()
                .map(|o| (o.expr, SerializeSignalKind::Output)),
        );
    }
    // ensure that non-state root expressions are always serialized
    for (expr, _) in todo.iter() {
        other_used.insert(*expr);
    }

    // add state root expressions
    todo.extend(
        init_exprs
            .iter()
            .map(|&e| (e, SerializeSignalKind::StateInit)),
    );
    todo.extend(
        next_exprs
            .iter()
            .map(|&e| (e, SerializeSignalKind::StateNext)),
    );

    // visit roots in the order in which they were declared
    todo.reverse();

    // visit expressions
    while let Some((expr_ref, kind)) = todo.pop() {
        if visited.contains(&expr_ref) {
            continue;
        }

        let expr = ctx.get(expr_ref);

        // check to see if all children are done
        let mut all_done = true;
        let mut num_children = 0;
        expr.for_each_child(|c| {
            if !visited.contains(c) {
                if all_done {
                    todo.push((expr_ref, kind)); // return expression to the todo list
                }
                all_done = false;
                // we need to visit the child first
                todo.push((*c, SerializeSignalKind::None));
            }
            num_children += 1;
        });

        if !all_done {
            continue;
        }

        // add to signal order if applicable
        if num_children > 0
            || matches!(
                kind,
                SerializeSignalKind::Input
                    | SerializeSignalKind::Output
                    | SerializeSignalKind::Constraint
                    | SerializeSignalKind::BadState
            )
        {
            let uses = Uses::new(expr_ref, &init_used, &next_used, &other_used);
            if uses.other {
                signal_order.push(RootInfo {
                    expr: expr_ref,
                    uses,
                    kind,
                });
            }
        }
        visited.insert(expr_ref);
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
