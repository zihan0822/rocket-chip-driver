// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use egg::*;
use patronus::expr::traversal::TraversalCmd;
use patronus::expr::{Context, ExprRef, TypeCheck, WidthInt};
use patronus_egraphs::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub fn generate_samples(
    rule_name: &str,
    rule: &Rewrite<Arith, ()>,
    max_width: WidthInt,
) -> Samples {
    let (lhs, rhs) = extract_patterns(rule).expect("failed to extract patterns from rewrite rule");
    println!("{}: {} => {}", rule_name, lhs, rhs);

    // analyze rule patterns
    let lhs_info = analyze_pattern(lhs);
    let rhs_info = analyze_pattern(lhs);
    let rule_info = lhs_info.merge(&rhs_info);
    println!("{:?}", rule_info);

    let num_assignments = rule_info.num_assignments(max_width);
    println!("There are {num_assignments} possible assignments for this rule.");

    // create context and start smt solver
    let mut ctx = Context::default();
    let solver: patronus::mc::SmtSolverCmd = patronus::mc::BITWUZLA_CMD;
    let mut smt_ctx = easy_smt::ContextBuilder::new()
        .solver(solver.name, solver.args)
        .replay_file(Some(std::fs::File::create("replay.smt").unwrap()))
        .build()
        .unwrap();
    smt_ctx.set_logic("QF_ABV").unwrap();

    // check all rewrites
    let mut samples = Samples::new(&rule_info);
    for assignment in rule_info.iter_assignments(max_width) {
        let lhs_expr = to_smt(&mut ctx, lhs, &lhs_info, &assignment);
        let rhs_expr = to_smt(&mut ctx, rhs, &rhs_info, &assignment);
        let is_eq = ctx.equal(lhs_expr, rhs_expr);
        let is_not_eq = ctx.not(is_eq);
        let smt_expr = patronus::smt::convert_expr(&smt_ctx, &ctx, is_not_eq, &|_| None);

        smt_ctx.push_many(1).unwrap();
        declare_vars(&mut smt_ctx, &ctx, is_not_eq);
        smt_ctx.assert(smt_expr).unwrap();
        let resp = smt_ctx.check().unwrap();
        smt_ctx.pop_many(1).unwrap();

        match resp {
            easy_smt::Response::Sat => samples.add(assignment, false),
            easy_smt::Response::Unsat => samples.add(assignment, true),
            easy_smt::Response::Unknown => println!("{assignment:?} => Unknown!"),
        }
    }
    samples
}

#[derive(Debug, Clone)]
pub struct Samples {
    vars: Vec<Var>,
    assignments: Vec<WidthInt>,
    is_equivalent: Vec<bool>,
}

impl Samples {
    fn new(rule: &RuleInfo) -> Self {
        let vars = rule.assignment_vars();
        let assignments = vec![];
        let is_equivalent = vec![];
        Self {
            vars,
            assignments,
            is_equivalent,
        }
    }
    fn add(&mut self, a: Assignment, is_equivalent: bool) {
        debug_assert_eq!(a.len(), self.vars.len());
        for ((a_var, a_value), &our_var) in a.into_iter().zip(self.vars.iter()) {
            assert_eq!(a_var, our_var);
            self.assignments.push(a_value);
        }
        self.is_equivalent.push(is_equivalent);
    }
    pub fn num_equivalent(&self) -> usize {
        self.is_equivalent.iter().filter(|e| **e).count()
    }

    pub fn num_unequivalent(&self) -> usize {
        self.is_equivalent.len() - self.num_equivalent()
    }

    pub fn iter(&self) -> impl Iterator<Item = (Assignment, bool)> + '_ {
        SamplesIter {
            samples: self,
            index: 0,
        }
    }
}

pub struct SamplesIter<'a> {
    samples: &'a Samples,
    index: usize,
}

impl<'a> Iterator for SamplesIter<'a> {
    type Item = (Assignment, bool);

    fn next(&mut self) -> Option<Self::Item> {
        let num_samples = self.samples.is_equivalent.len();
        if self.index >= num_samples {
            return None;
        }
        let num_vars = self.samples.vars.len();
        let a = self
            .samples
            .assignments
            .iter()
            .skip(self.index * num_vars)
            .zip(self.samples.vars.iter())
            .map(|(&value, &var)| (var, value))
            .collect::<Vec<_>>();
        let e = self.samples.is_equivalent[self.index];
        self.index += 1;
        Some((a, e))
    }
}

fn declare_vars(smt_ctx: &mut easy_smt::Context, ctx: &Context, expr: ExprRef) {
    // find all variables in the expression
    let mut vars = FxHashSet::default();
    patronus::expr::traversal::top_down(ctx, expr, |ctx, e| {
        if ctx[e].is_symbol() {
            vars.insert(e);
        }
        TraversalCmd::Continue
    });

    // declare them
    let mut vars = Vec::from_iter(vars);
    vars.sort();
    for v in vars.into_iter() {
        let expr = &ctx[v];
        let tpe = patronus::smt::convert_tpe(smt_ctx, expr.get_type(ctx));
        let name = expr.get_symbol_name(ctx).unwrap();
        smt_ctx
            .declare_const(name, tpe)
            .expect("failed to declare const");
    }
}

fn extract_patterns<L: Language>(
    rule: &Rewrite<L, ()>,
) -> Option<(&PatternAst<L>, &PatternAst<L>)> {
    let left = rule.searcher.get_pattern_ast()?;
    let right = rule.applier.get_pattern_ast()?;
    Some((left, right))
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct RuleInfo {
    width: Var,
    children: Vec<RuleChild>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct RuleChild {
    var: Var,
    width: Var,
    sign: Var,
}

pub type Assignment = Vec<(Var, WidthInt)>;

impl RuleInfo {
    fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        let children = union_vecs(&self.children, &other.children);
        Self {
            width: self.width,
            children,
        }
    }

    fn iter_assignments(&self, max_width: WidthInt) -> impl Iterator<Item = Assignment> + '_ {
        AssignmentIter {
            rule: self,
            index: 0,
            max_width,
        }
    }

    fn num_assignments(&self, max_width: WidthInt) -> u64 {
        let cl = self.children.len() as u32;
        let width_values = max_width as u64; // we do not use 0-bit
        2u64.pow(cl) * width_values.pow(1 + cl)
    }

    fn assignment_vars(&self) -> Vec<Var> {
        let mut out = vec![self.width];
        for child in self.children.iter() {
            out.push(child.width);
        }
        for child in self.children.iter() {
            out.push(child.sign);
        }
        out
    }
}

/// An iterator over all possivle assignments in a rule.
struct AssignmentIter<'a> {
    rule: &'a RuleInfo,
    index: u64,
    max_width: WidthInt,
}

impl<'a> Iterator for AssignmentIter<'a> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        let width_values = self.max_width as u64;
        let max = self.rule.num_assignments(self.max_width);
        if self.index == max {
            None
        } else {
            let mut out = Vec::with_capacity(1 + 2 * self.rule.children.len());
            let mut index = self.index;
            for width_var in [self.rule.width]
                .into_iter()
                .chain(self.rule.children.iter().map(|c| c.width))
            {
                let value = (index % width_values) as WidthInt + 1;
                index /= width_values;
                out.push((width_var, value))
            }
            for sign_var in self.rule.children.iter().map(|c| c.sign) {
                let value = (index % 2) as WidthInt;
                index /= 2;
                out.push((sign_var, value))
            }
            self.index += 1;
            Some(out)
        }
    }
}

/// Merges to vecs together like they are sets.
fn union_vecs<T: Clone + PartialEq + Ord>(a: &[T], b: &[T]) -> Vec<T> {
    let mut out = Vec::from(a);
    out.extend_from_slice(b);
    out.sort();
    out.dedup();
    out
}

/// Extracts the output width and all children including width and sign from an [[`egg::PatternAst`]].
/// Requires that the output width is name `?wo` and that the child width and sign are named like:
/// `?w{name}` and `?s{name}`.
fn analyze_pattern<L: Language>(pat: &PatternAst<L>) -> RuleInfo {
    let mut widths = FxHashMap::default();
    let mut signs = FxHashMap::default();
    let mut children = Vec::new();
    for element in pat.as_ref().iter() {
        if let &ENodeOrVar::Var(v) = element {
            // check name to determine the category
            let name = v.to_string();
            assert!(name.starts_with("?"), "expect all vars to start with `?`");
            let second_char = name.chars().nth(1).unwrap();
            match second_char {
                'w' => {
                    widths.insert(name, v);
                }
                's' => {
                    signs.insert(name, v);
                }
                _ => children.push(v),
            }
        }
    }
    let width = *widths
        .get("?wo")
        .expect("pattern is missing result width: `?wo`");
    let mut children = children
        .into_iter()
        .map(|c| {
            let name = c.to_string().chars().skip(1).collect::<String>();
            let width = *widths
                .get(&format!("?w{name}"))
                .unwrap_or_else(|| panic!("pattern is missing a width for `{name}`: `?w{name}`"));
            let sign = *signs
                .get(&format!("?s{name}"))
                .unwrap_or_else(|| panic!("pattern is missing a sign for `{name}`: `?s{name}`"));
            RuleChild {
                var: c,
                width,
                sign,
            }
        })
        .collect::<Vec<_>>();
    children.sort();
    RuleInfo { width, children }
}

/// Generates a patronus SMT expression from a pattern, rule info and assignment.
fn to_smt(
    ctx: &mut Context,
    pattern: &PatternAst<Arith>,
    rule: &RuleInfo,
    assignment: &Assignment,
) -> ExprRef {
    let subst = gen_substitution(ctx, rule, assignment);
    let arith_expr = instantiate_pattern(pattern, &subst);
    from_arith(ctx, &arith_expr)
}

/// Generates a complete substitution from an assignment.
fn gen_substitution(
    ctx: &mut Context,
    rule: &RuleInfo,
    assignment: &Assignment,
) -> FxHashMap<Var, Arith> {
    let assignment = FxHashMap::from_iter(assignment.clone());
    let mut out = FxHashMap::default();
    out.insert(rule.width, Arith::Width(assignment[&rule.width]));
    for child in rule.children.iter() {
        let width = assignment[&child.width];
        out.insert(child.width, Arith::Width(width));
        out.insert(child.sign, Arith::Signed(assignment[&child.sign] != 0));
        let name = child.var.to_string().chars().skip(1).collect::<String>();
        let symbol = ctx.bv_symbol(&name, width);
        let name_ref = ctx[symbol].get_symbol_name_ref().unwrap();
        let sym = ArithSymbol {
            name: name_ref,
            width,
        };
        out.insert(child.var, Arith::Symbol(sym));
    }
    out
}

/// Instantiates a pattern, replacing all vars with concrete e-nodes based on the given substitutions
fn instantiate_pattern<L: Language>(
    pattern: &PatternAst<L>,
    subst: &FxHashMap<Var, L>,
) -> RecExpr<L> {
    let mut out = RecExpr::default();
    for element in pattern.as_ref().iter() {
        let node = match element {
            ENodeOrVar::ENode(n) => n.clone(),
            ENodeOrVar::Var(v) => subst[v].clone(),
        };
        out.add(node);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use patronus::expr::TypeCheck;

    #[test]
    fn test_assignment_iter() {
        let r: Rewrite<Arith, ()> = rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)");
        let rule = &r;
        let (lhs, _rhs) =
            extract_patterns(rule).expect("failed to extract patterns from rewrite rule");

        // analyze rule patterns
        let lhs_info = analyze_pattern(lhs);
        let rhs_info = analyze_pattern(lhs);
        let rule_info = lhs_info.merge(&rhs_info);

        assert_eq!(
            rule_info.iter_assignments(8).count() as u64,
            rule_info.num_assignments(8)
        );
    }

    #[test]
    fn test_instantiate_pattern() {
        use std::str::FromStr;
        let rule: Rewrite<Arith, ()> = rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)");
        let (lhs, _rhs) =
            extract_patterns(&rule).expect("failed to extract patterns from rewrite rule");
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 1);
        let a_arith = ArithSymbol {
            name: ctx[a].get_symbol_name_ref().unwrap(),
            width: a.get_bv_type(&ctx).unwrap(),
        };
        let b = ctx.bv_symbol("b", 1);
        let b_arith = ArithSymbol {
            name: ctx[b].get_symbol_name_ref().unwrap(),
            width: b.get_bv_type(&ctx).unwrap(),
        };
        let subst = FxHashMap::from_iter([
            (Var::from_str("?wo").unwrap(), Arith::Width(2)),
            (Var::from_str("?wa").unwrap(), Arith::Width(a_arith.width)),
            (Var::from_str("?sa").unwrap(), Arith::Signed(true)),
            (Var::from_str("?a").unwrap(), Arith::Symbol(a_arith)),
            (Var::from_str("?wb").unwrap(), Arith::Width(b_arith.width)),
            (Var::from_str("?sb").unwrap(), Arith::Signed(true)),
            (Var::from_str("?b").unwrap(), Arith::Symbol(b_arith)),
        ]);

        assert_eq!(lhs.to_string(), "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)");
        let lhs_sub = instantiate_pattern(lhs, &subst);
        assert_eq!(
            lhs_sub.to_string(),
            "(+ 2 1 true \"StringRef(0):bv<1>\" 1 true \"StringRef(1):bv<1>\")"
        );
    }
}
