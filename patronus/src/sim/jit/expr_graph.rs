use crate::expr::{traversal, *};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::rc::Rc;

pub(crate) struct BottomUpExprGraph {
    pub(crate) roots: Vec<ExprRef>,
    /// For each expression node, tracks other nodes that directly depend on it
    pub(crate) node_dependents: FxHashMap<ExprRef, Vec<ExprRef>>,
}

impl BottomUpExprGraph {
    pub(crate) fn from_top_down_graph(ctx: &Context, top_down_roots: &[ExprRef]) -> Self {
        let mut bottom_up_roots = vec![];
        let mut node_dependents: FxHashMap<ExprRef, Vec<ExprRef>> =
            top_down_roots.iter().map(|&root| (root, vec![])).collect();

        traversal::top_down_without_reentry(ctx, top_down_roots, |ctx, current| {
            let mut has_children = false;
            ctx[current].for_each_child(|&child| {
                has_children = true;
                node_dependents.entry(child).or_default().push(current);
            });
            if !has_children {
                bottom_up_roots.push(current);
            }
            traversal::TraversalCmd::Continue
        });
        Self {
            roots: bottom_up_roots,
            node_dependents,
        }
    }

    /// Returns the default walker.
    /// There is no guarantee on the traversal order when multiple candidates are present.
    #[expect(dead_code)]
    pub(crate) fn walker(&self) -> BottomUpExprGraphWalker<'_> {
        BottomUpExprGraphWalker::new(self)
    }

    /// Returns a walker with custom candidate priority comparator.
    /// The internal representation is of candidates is a min-heap. Smaller value returned from `compare` will be prioritized.
    pub(crate) fn walker_with_sorted_fringe<F>(
        &self,
        compare: F,
    ) -> BiasedBottomUpExprGraphWalker<'_, F>
    where
        F: Fn(&ExprRef, &ExprRef) -> std::cmp::Ordering,
    {
        BiasedBottomUpExprGraphWalker::new(self, compare)
    }

    /// Returns an iterator of parent expr.
    /// Empty iterator will be returned if `expr` is not part of the graph.
    pub(crate) fn parent_expr_iter(&self, expr: ExprRef) -> impl Iterator<Item = ExprRef> {
        ParentExprIter {
            graph: self,
            todo: VecDeque::from_iter(
                self.node_dependents
                    .get(&expr)
                    .into_iter()
                    .flatten()
                    .copied(),
            ),
            visited: FxHashSet::default(),
        }
    }

    fn node_in_degree(&self) -> FxHashMap<ExprRef, usize> {
        let mut in_degree: FxHashMap<ExprRef, usize> =
            self.roots.iter().map(|&expr| (expr, 0)).collect();
        for &dependent in self
            .node_dependents
            .iter()
            .flat_map(|(_, dependents)| dependents)
        {
            *in_degree.entry(dependent).or_default() += 1;
        }
        in_degree
    }

    fn is_root_expr(&self, expr: ExprRef) -> bool {
        self.node_dependents
            .get(&expr)
            .is_some_and(|dependents| dependents.is_empty())
    }
}

pub(crate) struct BottomUpExprGraphWalker<'a> {
    todo: VecDeque<ExprRef>,
    graph: &'a BottomUpExprGraph,
    in_degree: FxHashMap<ExprRef, usize>,
}

impl<'a> BottomUpExprGraphWalker<'a> {
    fn new(graph: &'a BottomUpExprGraph) -> Self {
        Self {
            todo: Default::default(),
            graph,
            in_degree: graph.node_in_degree(),
        }
    }
}

impl Iterator for BottomUpExprGraphWalker<'_> {
    type Item = ExprRef;
    fn next(&mut self) -> Option<Self::Item> {
        self.todo.extend(
            self.in_degree
                .extract_if(|_, &mut degree| degree == 0)
                .map(|(expr, _)| expr),
        );
        let next = self.todo.pop_front()?;
        for dependent in &self.graph.node_dependents[&next] {
            *self.in_degree.get_mut(dependent).unwrap() -= 1;
        }
        Some(next)
    }
}

struct WeightedExprNode<F>
where
    F: Fn(&ExprRef, &ExprRef) -> std::cmp::Ordering,
{
    expr: ExprRef,
    compare: Rc<F>,
}

pub(crate) struct BiasedBottomUpExprGraphWalker<'a, F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    todo: BinaryHeap<WeightedExprNode<F>>,
    graph: &'a BottomUpExprGraph,
    in_degree: FxHashMap<ExprRef, usize>,
    fringe_compare: Rc<F>,
}

impl<'a, F> BiasedBottomUpExprGraphWalker<'a, F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    fn new(graph: &'a BottomUpExprGraph, compare: F) -> Self {
        Self {
            todo: BinaryHeap::default(),
            graph,
            in_degree: graph.node_in_degree(),
            fringe_compare: Rc::new(compare),
        }
    }
}

impl<'a, F> Iterator for BiasedBottomUpExprGraphWalker<'a, F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    type Item = ExprRef;
    fn next(&mut self) -> Option<Self::Item> {
        self.todo
            .extend(
                self.in_degree
                    .extract_if(|_, &mut degree| degree == 0)
                    .map(|(expr, _)| WeightedExprNode {
                        expr,
                        compare: Rc::clone(&self.fringe_compare),
                    }),
            );
        let next = self.todo.pop()?;
        for dependent in &self.graph.node_dependents[&next.expr] {
            *self.in_degree.get_mut(dependent).unwrap() -= 1;
        }
        Some(next.expr)
    }
}

impl<F> std::cmp::Ord for WeightedExprNode<F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.compare)(&self.expr, &other.expr).reverse()
    }
}

impl<F> std::cmp::PartialOrd for WeightedExprNode<F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F> std::cmp::PartialEq for WeightedExprNode<F>
where
    F: Fn(&ExprRef, &ExprRef) -> Ordering,
{
    fn eq(&self, other: &Self) -> bool {
        (self.compare)(&self.expr, &other.expr).is_eq()
    }
}

impl<F> std::cmp::Eq for WeightedExprNode<F> where F: Fn(&ExprRef, &ExprRef) -> Ordering {}

pub(crate) struct ParentExprIter<'a> {
    graph: &'a BottomUpExprGraph,
    todo: VecDeque<ExprRef>,
    visited: FxHashSet<ExprRef>,
}

impl Iterator for ParentExprIter<'_> {
    type Item = ExprRef;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.todo.pop_front()?;
        self.todo.extend(
            self.graph.node_dependents[&next]
                .iter()
                .filter(|&&parent| self.visited.insert(parent)),
        );
        Some(next)
    }
}

/// Checks whether `a` and `b` are at disjoint branch of a shared `Ite` node.
/// Returns `false` if `a` and `b` do not share any `Ite` parent node or they are at the same branch of the closest `Ite` parent.
pub(crate) fn at_disjoint_branch(
    ctx: &Context,
    graph: &BottomUpExprGraph,
    mut a: ExprRef,
    mut b: ExprRef,
) -> bool {
    let a_parents: FxHashSet<_> = graph.parent_expr_iter(a).collect();
    let b_parents: FxHashSet<_> = graph.parent_expr_iter(b).collect();
    let mut is_ancestor = false;
    if b_parents.contains(&a) {
        is_ancestor = true;
    } else if a_parents.contains(&b) {
        is_ancestor = true;
        std::mem::swap(&mut a, &mut b);
    }

    if is_ancestor {
        return false;
    }
    a_parents
        .intersection(&b_parents)
        .filter(|&&parent| graph.is_root_expr(parent))
        .all(|&root| {
            find_lowest_common_ite(ctx, root, a, b)
                .is_some_and(|(_, operand_a, operand_b)| operand_a != operand_b)
        })
}

/// Find the lowest common ite ancestor for the given pair of exprs in linear time.
/// The number of `Ite` node is usually small in an expression graph, O(n) algorithm currently works fine.
/// Returns a tuple of: shared ite parent node and top arm expression a, b belongs to.
/// `a` and `b` should not have ancestor relationship.
fn find_lowest_common_ite(
    ctx: &Context,
    root: ExprRef,
    a: ExprRef,
    b: ExprRef,
) -> Option<(ExprRef, ExprRef, ExprRef)> {
    let bottom_up_expr_graph = BottomUpExprGraph::from_top_down_graph(ctx, &[root]);
    let parent_ites_a =
        find_parent_ites_with_top_arm_expr(ctx, bottom_up_expr_graph.parent_expr_iter(a), a);
    let parent_ites_b: FxHashMap<_, _> =
        find_parent_ites_with_top_arm_expr(ctx, bottom_up_expr_graph.parent_expr_iter(b), b)
            .collect();
    for (ite_a, arm_a) in parent_ites_a {
        if let Some(&arm_b) = parent_ites_b.get(&ite_a) {
            return Some((ite_a, arm_a, arm_b));
        }
    }
    None
}

fn find_parent_ites_with_top_arm_expr(
    ctx: &Context,
    parent_iter: impl Iterator<Item = ExprRef>,
    start: ExprRef,
) -> impl Iterator<Item = (ExprRef, ExprRef)> {
    parent_iter
        .scan(start, |top, parent| {
            let next = (*top, parent);
            *top = parent;
            Some(next)
        })
        .filter(|&(_, parent)| matches!(ctx[parent], Expr::ArrayIte { .. }))
}
