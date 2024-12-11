// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::rewrites::ArithRewrite;
use egg::*;
use indicatif::ProgressBar;
use patronus::expr::traversal::TraversalCmd;
use patronus::expr::{Context, ExprRef, TypeCheck, WidthInt};
use patronus_egraphs::*;
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

pub fn get_rule_info(rule: &ArithRewrite) -> RuleInfo {
    let (lhs, rhs) = rule.patterns();
    let lhs_info = analyze_pattern(lhs);
    let rhs_info = analyze_pattern(rhs);
    lhs_info.merge(&rhs_info)
}

pub fn generate_samples(
    rule: &ArithRewrite,
    max_width: WidthInt,
    show_progress: bool,
    dump_smt: bool,
) -> Samples {
    let (lhs, rhs) = rule.patterns();
    let lhs_info = analyze_pattern(lhs);
    let rhs_info = analyze_pattern(rhs);
    let rule_info = lhs_info.merge(&rhs_info);

    let num_assignments = rule_info.num_assignments(max_width);
    println!("There are {num_assignments} possible assignments for this rule.");

    // progress indicator
    let prog = if show_progress {
        Some(ProgressBar::new(rule_info.num_assignments(max_width)))
    } else {
        None
    };

    // split up work across threads
    let num_threads = rayon::current_num_threads();
    let assignment_range = 0..rule_info.num_assignments(max_width);
    let assignments_per_thread = assignment_range.end as usize / num_threads;

    // check all rewrites in parallel
    let samples = assignment_range
        .collect::<Vec<_>>()
        .par_chunks(assignments_per_thread)
        .map(|assignment_indices| {
            // create context and samples
            let mut ctx = Context::default();
            let mut smt_ctx = start_solver(dump_smt);
            let mut samples = Samples::new(&rule_info);

            for &assignment_index in assignment_indices.iter() {
                if let Some(p) = &prog {
                    p.inc(1);
                }
                let assignment = rule_info.get_assignment(max_width, assignment_index);
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
        })
        .collect::<Vec<_>>();

    // merge results from different threads
    samples
        .into_par_iter()
        .reduce(|| Samples::new(&rule_info), Samples::merge)
}

fn start_solver(dump_smt: bool) -> easy_smt::Context {
    let solver: patronus::mc::SmtSolverCmd = patronus::mc::BITWUZLA_CMD;
    let dump_file = if dump_smt {
        Some(std::fs::File::create("replay.smt").unwrap())
    } else {
        None
    };
    let mut smt_ctx = easy_smt::ContextBuilder::new()
        .solver(solver.name, solver.args)
        .replay_file(dump_file)
        .build()
        .unwrap();
    smt_ctx.set_logic("QF_ABV").unwrap();
    smt_ctx
}

#[derive(Debug, Clone)]
pub struct Samples {
    vars: Vec<Var>,
    assignments: Vec<WidthInt>,
    is_equivalent: Vec<bool>,
}

/// Works around the fact that `Var` cannot be serialized/deserialized
#[derive(Serialize, Deserialize)]
struct SamplesSerde {
    vars: Vec<String>,
    assignments: Vec<WidthInt>,
    is_equivalent: Vec<bool>,
}

impl From<Samples> for SamplesSerde {
    fn from(value: Samples) -> Self {
        let vars = value.vars.into_iter().map(|v| v.to_string()).collect();
        Self {
            vars,
            assignments: value.assignments,
            is_equivalent: value.is_equivalent,
        }
    }
}

impl From<SamplesSerde> for Samples {
    fn from(value: SamplesSerde) -> Self {
        let vars = value.vars.into_iter().map(|v| v.parse().unwrap()).collect();
        Self {
            vars,
            assignments: value.assignments,
            is_equivalent: value.is_equivalent,
        }
    }
}

impl Samples {
    fn new(rule: &RuleInfo) -> Self {
        let vars = rule.assignment_vars().collect();
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
    pub fn merge(mut a: Self, mut b: Self) -> Self {
        debug_assert_eq!(a.vars, b.vars);
        a.assignments.append(&mut b.assignments);
        a.is_equivalent.append(&mut b.is_equivalent);
        a
    }

    pub fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        self.vars.iter().cloned()
    }

    pub fn to_json(self, out: &mut impl std::io::Write) -> serde_json::error::Result<()> {
        let s: SamplesSerde = self.into();
        serde_json::to_writer_pretty(out, &s)
    }

    pub fn from_json(input: &mut impl std::io::Read) -> serde_json::error::Result<Self> {
        let s: SamplesSerde = serde_json::from_reader(input)?;
        Ok(s.into())
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

// fn extract_condition<L: Language>(
//     rule: &Rewrite<L, ()>,
// ) {
//     rule.applier.apply_matches()
// }

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RuleInfo {
    /// width parameters
    widths: Vec<Var>,
    /// sign parameters
    signs: Vec<Var>,
    /// all actual expression symbols in the rule which we need to plug in
    /// if we want to check for equivalence
    symbols: Vec<RuleSymbol>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum VarOrConst {
    C(WidthInt),
    V(Var),
}

/// a unique symbol in a rule, needs to be replaced with an SMT bit-vector symbol for equivalence checks
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct RuleSymbol {
    var: Var,
    width: VarOrConst,
    sign: VarOrConst,
}

pub type Assignment = Vec<(Var, WidthInt)>;

impl RuleInfo {
    pub fn signs(&self) -> impl Iterator<Item = Var> + '_ {
        self.signs.iter().cloned()
    }
    pub fn widths(&self) -> impl Iterator<Item = Var> + '_ {
        self.widths.iter().cloned()
    }
}

impl RuleInfo {
    fn merge(&self, other: &Self) -> Self {
        let widths = union_vecs(&self.widths, &other.widths);
        let signs = union_vecs(&self.signs, &other.signs);
        let symbols = union_vecs(&self.symbols, &other.symbols);
        Self {
            widths,
            signs,
            symbols,
        }
    }

    #[allow(dead_code)]
    fn iter_assignments(&self, max_width: WidthInt) -> impl Iterator<Item = Assignment> + '_ {
        AssignmentIter {
            rule: self,
            index: 0,
            max_width,
        }
    }

    fn num_assignments(&self, max_width: WidthInt) -> u64 {
        let width_values = max_width as u64; // we do not use 0-bit
        2u64.pow(self.signs.len() as u32) * width_values.pow(self.widths.len() as u32)
    }

    /// gets the assignment `ii` where `num_asignments > index >= 0`
    fn get_assignment(&self, max_width: WidthInt, mut index: u64) -> Assignment {
        debug_assert!(self.num_assignments(max_width) > index);
        let width_values = max_width as u64;
        let mut out = Vec::with_capacity(1 + 2 * self.symbols.len());
        for &width_var in self.widths.iter() {
            let value = (index % width_values) as WidthInt + 1;
            index /= width_values;
            out.push((width_var, value))
        }
        for &sign_var in self.signs.iter() {
            let value = (index % 2) as WidthInt;
            index /= 2;
            out.push((sign_var, value))
        }
        out
    }

    fn assignment_vars(&self) -> impl Iterator<Item = Var> + '_ {
        self.widths
            .iter()
            .cloned()
            .chain(self.signs.iter().cloned())
    }
}

/// An iterator over all possivle assignments in a rule.
#[allow(dead_code)]
struct AssignmentIter<'a> {
    rule: &'a RuleInfo,
    index: u64,
    max_width: WidthInt,
}

impl<'a> Iterator for AssignmentIter<'a> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        let max = self.rule.num_assignments(self.max_width);
        if self.index == max {
            None
        } else {
            let out = self.rule.get_assignment(self.max_width, self.index);
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

#[inline]
pub fn get_var_name(v: &Var) -> Option<String> {
    let name = v.to_string();
    if name.starts_with('?') {
        Some(name.chars().skip(1).collect())
    } else {
        None
    }
}

/// Extracts the output width and all children including width and sign from an [[`egg::PatternAst`]].
/// Requires that the output width is name `?wo` and that the child width and sign are named like:
/// `?w{name}` and `?s{name}`.
fn analyze_pattern(pat: &PatternAst<Arith>) -> RuleInfo {
    let mut widths = vec![];
    let mut signs = vec![];
    let mut symbols = Vec::new();
    for element in pat.as_ref().iter() {
        match &element {
            ENodeOrVar::Var(v) => {
                // collect information on variables
                let name = v.to_string();
                assert!(name.starts_with("?"), "expect all vars to start with `?`");
                let second_char = name.chars().nth(1).unwrap();
                match second_char {
                    'w' => widths.push(*v),
                    's' => signs.push(*v),
                    _ => {} // ignore
                }
            }
            ENodeOrVar::ENode(n) => {
                // bin op pattern
                if let [_w, w_a, s_a, a, w_b, s_b, b] = n.children() {
                    if let Some(s) = symbol_from_pattern(pat, *a, *w_a, *s_a) {
                        symbols.push(s);
                    }
                    if let Some(s) = symbol_from_pattern(pat, *b, *w_b, *s_b) {
                        symbols.push(s);
                    }
                }
            }
        }
    }

    widths.sort();
    widths.dedup();
    signs.sort();
    signs.dedup();
    symbols.sort();
    symbols.dedup();
    RuleInfo {
        widths,
        signs,
        symbols,
    }
}

fn symbol_from_pattern(pat: &PatternAst<Arith>, a: Id, w: Id, s: Id) -> Option<RuleSymbol> {
    if let ENodeOrVar::Var(var) = pat[a] {
        let width = width_const_from_pattern(pat, w);
        let sign = width_const_from_pattern(pat, s);
        Some(RuleSymbol { var, width, sign })
    } else {
        None
    }
}

fn width_const_from_pattern(pat: &PatternAst<Arith>, id: Id) -> VarOrConst {
    match &pat[id] {
        ENodeOrVar::ENode(node) => match node {
            &Arith::WidthConst(w) => VarOrConst::C(w),
            _ => unreachable!("not a width!"),
        },
        ENodeOrVar::Var(var) => VarOrConst::V(*var),
    }
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
    for &width_var in rule.widths.iter() {
        out.insert(width_var, Arith::WidthConst(assignment[&width_var]));
    }
    for &sign_var in rule.signs.iter() {
        debug_assert!(assignment[&sign_var] <= 1);
        out.insert(sign_var, Arith::WidthConst(assignment[&sign_var]));
    }
    for child in rule.symbols.iter() {
        let width = match child.width {
            VarOrConst::C(w) => w,
            VarOrConst::V(v) => assignment[&v],
        };
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
            (Var::from_str("?wo").unwrap(), Arith::WidthConst(2)),
            (
                Var::from_str("?wa").unwrap(),
                Arith::WidthConst(a_arith.width),
            ),
            (Var::from_str("?sa").unwrap(), Arith::WidthConst(1)),
            (Var::from_str("?a").unwrap(), Arith::Symbol(a_arith)),
            (
                Var::from_str("?wb").unwrap(),
                Arith::WidthConst(b_arith.width),
            ),
            (Var::from_str("?sb").unwrap(), Arith::WidthConst(1)),
            (Var::from_str("?b").unwrap(), Arith::Symbol(b_arith)),
        ]);

        assert_eq!(lhs.to_string(), "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)");
        let lhs_sub = instantiate_pattern(lhs, &subst);
        assert_eq!(
            lhs_sub.to_string(),
            "(+ 2 1 1 \"StringRef(0):bv<1>\" 1 1 \"StringRef(1):bv<1>\")"
        );
    }
}
