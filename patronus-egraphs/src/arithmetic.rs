// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecOps;
use egg::{
    define_language, ConditionalApplier, ENodeOrVar, Id, Language, Pattern, PatternAst, RecExpr,
    Rewrite, Subst, Var,
};
use patronus::expr::*;
use std::cmp::{max, Ordering};
use std::fmt::{Display, Formatter};
use std::str::FromStr;

define_language! {
    /// Intermediate expression language for bit vector arithmetic rewrites.
    /// Inspired by: "ROVER: RTL Optimization via Verified E-Graph Rewriting" (TCAD'24)
    /// arguments for binop: w, w_a, s_a, a, w_b, s_b, b
    pub enum Arith {
        // operations on actual bit-vec values
        "+" = Add([Id; 7]),
        "-" = Sub([Id; 7]),
        "*" = Mul([Id; 7]),
        "<<" = LeftShift([Id; 7]),
        ">>" = RightShift([Id; 7]),
        ">>>" = ArithmeticRightShift([Id; 7]),
        // operations on widths
        "max+1" = WidthMaxPlus1([Id; 2]),
        Width(WidthValue),
        Sign(Sign),
        // not a width, but a value constant
        Const(u64),
        Symbol(String),
    }
}

/// our version of the egg re-write macro
macro_rules! arith_rewrite {
    (
        $name:expr;
        $lhs:expr => $rhs:expr
    ) => {{
        ArithRewrite::new::<&str>($name, $lhs, $rhs, [], None)
    }};
    (
        $name:expr;
        $lhs:expr => $rhs:expr;
        if $vars:expr, $cond:expr
    ) => {{
        ArithRewrite::new($name, $lhs, $rhs, $vars, Some($cond))
    }};
}

/// Generate our ROVER inspired rewrite rules.
pub fn create_rewrites() -> Vec<ArithRewrite> {
    vec![
        // a + b <=> b + a
        arith_rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
        // (a << b) << x <=> a << (b + c)
        arith_rewrite!("merge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            // we do not want (b + c) to wrap, because in that case the result would always be zero
            // the value being shifted has to be consistently signed or unsigned
            "(<< ?wo ?wab ?sa (<< ?wab ?wa ?sa ?a ?wb unsign ?b) ?wc unsign ?c)" =>
            "(<< ?wo ?wa ?sa ?a (max+1 ?wb ?wc) unsign (+ (max+1 ?wb ?wc) ?wb unsign ?b ?wc unsign ?c))";
            // wab >= wo
            if["?wo", "?wab"], |w| w[1] >= w[0]),
        // a * 2 <=> a + a
        arith_rewrite!("mult-to-add";
            "(* ?wo ?wa ?sa ?a ?wb ?sb 2)" =>
            "(+ ?wo ?wa ?sa ?a ?wa ?sa ?a)";
            // (!sb && wb > 1) || (sb && wb > 2) || (wo <= wb)
           if["?wb", "?sb", "?wo"], |w| (w[1] == 0 && w[0] > 1) || (w[1] == 1 && w[0] > 2) || w[2] <= w[0]),
    ]
}

/// Wrapper struct in order to do custom parsing.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct WidthValue(WidthInt);

// this allows us to use ArithWidthConst as an argument to ctx.bit_vec_val
impl From<WidthValue> for u128 {
    fn from(value: WidthValue) -> Self {
        value.0 as u128
    }
}

impl From<WidthValue> for WidthInt {
    fn from(value: WidthValue) -> Self {
        value.0
    }
}

impl From<WidthInt> for Arith {
    fn from(value: WidthInt) -> Self {
        Arith::Width(WidthValue(value))
    }
}

impl FromStr for WidthValue {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(suffix) = s.strip_prefix("W<") {
            if let Some(value) = suffix.strip_suffix(">") {
                match value.parse() {
                    Err(_) => Err(()),
                    Ok(w) => Ok(Self(w)),
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl Display for WidthValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "W<{}>", self.0)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum Sign {
    Signed,
    Unsigned,
}

// this allows us to use Sign as an argument to ctx.bit_vec_val
impl From<Sign> for u128 {
    fn from(value: Sign) -> Self {
        let w: WidthInt = value.into();
        w as u128
    }
}

impl From<Sign> for WidthInt {
    fn from(value: Sign) -> Self {
        match value {
            Sign::Signed => 1,
            Sign::Unsigned => 0,
        }
    }
}

impl From<Sign> for Arith {
    fn from(value: Sign) -> Self {
        Arith::Sign(value)
    }
}

impl FromStr for Sign {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sign" => Ok(Self::Signed),
            "unsign" => Ok(Self::Unsigned),
            _ => Err(()),
        }
    }
}

impl Display for Sign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Sign::Signed => write!(f, "sign"),
            Sign::Unsigned => write!(f, "unsign"),
        }
    }
}

/// Convert from our internal IR to the arithmetic expression IR suitable for rewrites.
pub fn to_arith(ctx: &Context, e: ExprRef) -> egg::RecExpr<Arith> {
    let mut out = egg::RecExpr::default();
    traversal::bottom_up_multi_pat(
        ctx,
        e,
        |ctx, expr, children| {
            // ignore any sing or zero extension when calculating the children
            expr.for_each_child(|c| {
                children.push(remove_ext(ctx, *c).0);
            });
        },
        |_ctx, expr, children| match ctx[expr].clone() {
            Expr::BVSymbol { name, .. } => out.add(Arith::Symbol(ctx[name].to_string())),
            Expr::BVAdd(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Add,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVSub(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Sub,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVMul(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::Mul,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVShiftLeft(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::LeftShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVShiftRight(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::RightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            Expr::BVArithmeticShiftRight(a, b, width) => convert_bin_op(
                ctx,
                &mut out,
                Arith::ArithmeticRightShift,
                a,
                b,
                width,
                children[0],
                children[1],
            ),
            _ => todo!("{}", expr.serialize_to_str(ctx)),
        },
    );
    out
}

#[allow(clippy::too_many_arguments)]
fn convert_bin_op(
    ctx: &Context,
    out: &mut RecExpr<Arith>,
    op: fn([Id; 7]) -> Arith,
    a: ExprRef,
    b: ExprRef,
    width_out: WidthInt,
    converted_a: Id,
    converted_b: Id,
) -> Id {
    // see the actual children (excluding any extensions) and determine sign
    let (base_a, sign_a) = remove_ext(ctx, a);
    let width_a = base_a.get_bv_type(ctx).unwrap();
    let (base_b, sign_b) = remove_ext(ctx, b);
    let width_b = base_b.get_bv_type(ctx).unwrap();
    debug_assert_eq!(width_out, a.get_bv_type(ctx).unwrap());
    debug_assert_eq!(width_out, b.get_bv_type(ctx).unwrap());
    // convert signedness and widths into e-nodes
    let width_out = out.add(width_out.into());
    let width_a = out.add(width_a.into());
    let width_b = out.add(width_b.into());
    let sign_a = out.add(sign_a.into());
    let sign_b = out.add(sign_b.into());
    out.add(op([
        width_out,
        width_a,
        sign_a,
        converted_b,
        width_b,
        sign_b,
        converted_a,
    ]))
}

/// Removes any sign or zero extend expressions and returns whether the removed extension was signed.
fn remove_ext(ctx: &Context, e: ExprRef) -> (ExprRef, Sign) {
    match ctx[e] {
        Expr::BVZeroExt { e, .. } => (remove_ext(ctx, e).0, Sign::Unsigned),
        Expr::BVSignExt { e, .. } => (remove_ext(ctx, e).0, Sign::Signed),
        _ => (e, Sign::Unsigned),
    }
}

/// Convert from the arithmetic expression IR back to our internal SMTLib based IR.
pub fn from_arith(ctx: &mut Context, expr: &RecExpr<Arith>) -> ExprRef {
    let expressions = expr.as_ref();
    let mut todo = vec![(expressions.len() - 1, false, 0)];
    let mut stack = Vec::with_capacity(4);
    let mut child_widths = Vec::with_capacity(8);

    while let Some((e, bottom_up, expected_width)) = todo.pop() {
        let expr = &expressions[e];

        // Check if there are children that we need to compute first.
        if !bottom_up && !expr.children().is_empty() {
            todo.push((e, true, expected_width));
            get_child_widths(e, expressions, &mut child_widths);
            for (child_id, expected_w) in expr.children().iter().zip(child_widths.iter()) {
                todo.push((usize::from(*child_id), false, *expected_w));
            }
            child_widths.clear();
            continue;
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let result = match expr {
            Arith::Symbol(name) => {
                debug_assert!(expected_width > 0, "unknown width for symbol `{name}`!");
                ctx.bv_symbol(name, expected_width)
            }
            Arith::Add(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.add(a, b)),
            Arith::Sub(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.sub(a, b)),
            Arith::Mul(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.mul(a, b)),
            Arith::LeftShift(_) => {
                patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.shift_left(a, b))
            }
            Arith::RightShift(_) => {
                patronus_bin_op(ctx, &mut stack, |ctx, a, b| ctx.shift_right(a, b))
            }
            Arith::ArithmeticRightShift(_) => patronus_bin_op(ctx, &mut stack, |ctx, a, b| {
                ctx.arithmetic_shift_right(a, b)
            }),
            Arith::WidthMaxPlus1(_) => {
                let a = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                let b = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
                ctx.bit_vec_val(max(a, b) + 1, 32)
            }
            Arith::Width(width) => ctx.bit_vec_val(*width, 32),
            Arith::Sign(sign) => ctx.bit_vec_val(*sign, 1),
            Arith::Const(value) => {
                debug_assert!(expected_width > 0, "unknown width for constant `{value}`!");
                // patronus will normally throw an error, if the value does not fit into the width
                // however, in our case, we want to just ignore the bits that get lost
                let value = if expected_width < u64::BITS {
                    *value & ((1u64 << expected_width) - 1)
                } else {
                    *value
                };
                ctx.bit_vec_val(value, expected_width)
            }
        };
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

/// extracts the expected widths of all proper child expressions
fn get_child_widths(root: usize, expressions: &[Arith], out: &mut Vec<WidthInt>) {
    debug_assert!(out.is_empty());
    let expr = &expressions[root];
    if is_bin_op(expr) {
        // w, w_a, s_a, a, w_b, s_b, b
        let a_width = get_width(usize::from(expr.children()[1]), expressions);
        let b_width = get_width(usize::from(expr.children()[4]), expressions);
        // we set don't cares to zero
        out.extend_from_slice(&[0, 0, 0, a_width, 0, 0, b_width]);
    } else {
        match expr {
            // calculated width
            Arith::WidthMaxPlus1(_) => {
                // widths are always propagated as 32-bit values
                out.extend_from_slice(&[32, 32]);
            }
            _ => {
                // otherwise there is nothing to do
                debug_assert!(expr.children().is_empty(), "{expr:?}")
            }
        }
    }
}

fn get_width(root: usize, expressions: &[Arith]) -> WidthInt {
    match &expressions[root] {
        Arith::Width(w) => w.0,
        Arith::WidthMaxPlus1([a, b]) => {
            let a = get_width(usize::from(*a), expressions);
            let b = get_width(usize::from(*b), expressions);
            max(a, b) + 1
        }
        other => todo!("calculate width for {other:?}"),
    }
}

fn is_bin_op(a: &Arith) -> bool {
    matches!(
        a,
        Arith::Add(_)
            | Arith::Sub(_)
            | Arith::Mul(_)
            | Arith::LeftShift(_)
            | Arith::RightShift(_)
            | Arith::ArithmeticRightShift(_)
    )
}

fn patronus_bin_op(
    ctx: &mut Context,
    stack: &mut Vec<ExprRef>,
    op: fn(&mut Context, ExprRef, ExprRef) -> ExprRef,
) -> ExprRef {
    // get parameters from stack
    let wo = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let wa = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sa = get_u64(ctx, stack.pop().unwrap()) != 0;
    let a = stack.pop().unwrap();
    let wb = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sb = get_u64(ctx, stack.pop().unwrap()) != 0;
    let b = stack.pop().unwrap();

    // slice and extend appropriately
    let arg_max_width = max(wa, wb);
    let calc_width = max(arg_max_width, wo);
    let a = extend(ctx, a, calc_width, wa, sa);
    let b = extend(ctx, b, calc_width, wb, sb);
    let res = op(ctx, a, b);
    if calc_width == wo {
        res
    } else {
        debug_assert!(calc_width > wo);
        ctx.slice(res, wo - 1, 0)
    }
}

fn get_u64(ctx: &Context, e: ExprRef) -> u64 {
    match &ctx[e] {
        Expr::BVLiteral(value) => value.get(ctx).to_u64().unwrap(),
        other => unreachable!(
            "{} is not a bit vector literal!",
            other.serialize_to_str(ctx)
        ),
    }
}

fn extend(
    ctx: &mut Context,
    expr: ExprRef,
    w_out: WidthInt,
    w_in: WidthInt,
    signed: bool,
) -> ExprRef {
    debug_assert_eq!(
        expr.get_bv_type(ctx).unwrap(),
        w_in,
        "{}",
        expr.serialize_to_str(ctx)
    );
    match w_out.cmp(&w_in) {
        Ordering::Less => unreachable!("cannot extend from {w_in} to {w_out}"),
        Ordering::Equal => expr,
        Ordering::Greater if !signed => ctx.zero_extend(expr, w_out - w_in),
        Ordering::Greater => ctx.sign_extend(expr, w_out - w_in),
    }
}

pub struct ArithRewrite {
    name: String,
    /// most general lhs pattern
    lhs: Pattern<Arith>,
    /// rhs pattern with all widths derived from the lhs, maybe be the same as rhs
    rhs_derived: Pattern<Arith>,
    /// variables use by the condition
    cond_vars: Vec<Var>,
    /// condition of the re_write
    cond: Option<fn(&[WidthInt]) -> bool>,
}

impl ArithRewrite {
    fn new<S: AsRef<str>>(
        name: &str,
        lhs: &str,
        rhs_derived: &str,
        cond_vars: impl IntoIterator<Item = S>,
        cond: Option<fn(&[WidthInt]) -> bool>,
    ) -> Self {
        let cond_vars = cond_vars
            .into_iter()
            .map(|n| n.as_ref().parse().unwrap())
            .collect();
        let lhs = lhs.parse::<_>().unwrap();
        check_width_consistency(&lhs);
        let rhs_derived = rhs_derived.parse::<_>().unwrap();
        check_width_consistency(&rhs_derived);
        Self {
            name: name.to_string(),
            lhs,
            rhs_derived,
            cond,
            cond_vars,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn patterns(&self) -> (&PatternAst<Arith>, &PatternAst<Arith>) {
        (&self.lhs.ast, &self.rhs_derived.ast)
    }

    pub fn to_egg(&self) -> Vec<Rewrite<Arith, ()>> {
        // TODO: support bi-directional rules
        if let Some(cond) = self.cond {
            let vars: Vec<Var> = self.cond_vars.clone();
            let condition = move |egraph: &mut EGraph, _, subst: &Subst| {
                let values: Vec<WidthInt> = vars
                    .iter()
                    .map(|v| get_const_width_or_sign(egraph, subst, *v))
                    .collect();
                cond(values.as_slice())
            };
            let cond_app = ConditionalApplier {
                condition,
                applier: self.rhs_derived.clone(),
            };
            vec![Rewrite::new(self.name.clone(), self.lhs.clone(), cond_app).unwrap()]
        } else {
            vec![Rewrite::new(
                self.name.clone(),
                self.lhs.clone(),
                self.rhs_derived.clone(),
            )
            .unwrap()]
        }
    }

    pub fn eval_condition(&self, a: &[(Var, WidthInt)]) -> bool {
        if let Some(cond) = self.cond {
            let values: Vec<WidthInt> = self
                .cond_vars
                .iter()
                .map(|v| a.iter().find(|(k, _)| k == v).unwrap().1)
                .collect();
            cond(values.as_slice())
        } else {
            // unconditional rewrite
            true
        }
    }
}

type EGraph = egg::EGraph<Arith, ()>;

/// Finds a width or sign constant in the e-class referred to by the substitution
/// and returns its value. Errors if no such constant can be found.
fn get_const_width_or_sign(egraph: &EGraph, subst: &Subst, v: Var) -> WidthInt {
    egraph[subst[v]]
        .nodes
        .iter()
        .flat_map(|n| match n {
            Arith::Width(w) => Some((*w).into()),
            Arith::Sign(s) => Some((*s).into()),
            _ => None,
        })
        .next()
        .expect("failed to find constant width")
}

/// Checks that input and output widths of operations are consistent.
fn check_width_consistency(pattern: &Pattern<Arith>) {
    let exprs = pattern.ast.as_ref();
    for e_node_or_var in exprs.iter() {
        if let ENodeOrVar::ENode(expr) = e_node_or_var {
            if is_bin_op(expr) {
                // w, w_a, s_a, a, w_b, s_b, b
                let a_width_id = usize::from(expr.children()[1]);
                let a_id = usize::from(expr.children()[3]);
                if let Some(a_op_out_width_id) = get_output_width_id(&exprs[a_id]) {
                    assert_eq!(
                        a_width_id, a_op_out_width_id,
                        "In `{expr}`, subexpression `{}` has inconsistent width: {} != {}",
                        &exprs[a_id], &exprs[a_width_id], &exprs[a_op_out_width_id]
                    );
                }
                let b_width_id = usize::from(expr.children()[4]);
                let b_id = usize::from(expr.children()[6]);
                if let Some(b_op_out_width_id) = get_output_width_id(&exprs[b_id]) {
                    assert_eq!(
                        b_width_id, b_op_out_width_id,
                        "In `{expr}`, subexpression `{}` has inconsistent width: {} != {}",
                        &exprs[b_id], &exprs[b_width_id], &exprs[b_op_out_width_id]
                    );
                }
            }
        }
    }
}

/// returns the egg id of the output width, if `expr` has one
fn get_output_width_id(expr: &ENodeOrVar<Arith>) -> Option<usize> {
    if let ENodeOrVar::ENode(expr) = expr {
        if is_bin_op(expr) {
            // w, w_a, s_a, a, w_b, s_b, b
            Some(usize::from(expr.children()[0]))
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_path_verification_fig_1() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("A", 16);
        let b = ctx.bv_symbol("B", 16);
        let m = ctx.bv_symbol("M", 4);
        let n = ctx.bv_symbol("N", 4);
        let spec = ctx.build(|c| {
            c.mul(
                c.zero_extend(c.shift_left(c.zero_extend(a, 15), c.zero_extend(m, 27)), 32),
                c.zero_extend(c.shift_left(c.zero_extend(b, 15), c.zero_extend(n, 27)), 32),
            )
        });
        let implementation = ctx.build(|c| {
            c.shift_left(
                c.zero_extend(c.mul(c.zero_extend(a, 16), c.zero_extend(b, 16)), 31),
                c.zero_extend(c.add(c.zero_extend(m, 1), c.zero_extend(n, 1)), 58),
            )
        });

        let spec_e = to_arith(&ctx, spec);
        let impl_e = to_arith(&ctx, implementation);

        // convert back into out IR
        let spec_back = from_arith(&mut ctx, &spec_e);
        let impl_back = from_arith(&mut ctx, &impl_e);

        // because of hash consing, we should get the exact same expr ref back
        assert_eq!(spec_back, spec);
        assert_eq!(impl_back, implementation);
    }

    #[test]
    fn test_rewrites() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("A", 16);
        let b = ctx.bv_symbol("B", 16);
        let in_smt_expr = ctx.add(a, b);
        assert_eq!(in_smt_expr.serialize_to_str(&ctx), "add(A, B)");

        // run egraph operations
        let egg_expr_in = to_arith(&ctx, in_smt_expr);
        let egg_rewrites: Vec<Rewrite<_, _>> = create_rewrites()
            .into_iter()
            .map(|r| r.to_egg())
            .reduce(|mut a, mut b| {
                a.append(&mut b);
                a
            })
            .unwrap();
        let runner = egg::Runner::default()
            .with_expr(&egg_expr_in)
            .run(&egg_rewrites);

        // check how many different nodes are representing the root node now
        let root = runner.roots[0];
        let root_nodes = &runner.egraph[root].nodes;
        assert_eq!(
            root_nodes.len(),
            2,
            "there should be two nodes if the rule has been applied"
        );
    }
}
