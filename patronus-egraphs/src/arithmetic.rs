// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::BitVecOps;
use egg::{define_language, rewrite, Id, Language, RecExpr, Var};
use patronus::expr::*;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::str::FromStr;

define_language! {
    /// Intermediate expression language for bit vector arithmetic rewrites.
    /// Inspired by: "ROVER: RTL Optimization via Verified E-Graph Rewriting" (TCAD'24)
    /// arguments for binop: w, w_a, s_a, a, w_b, s_b, b
    pub enum Arith {
        "+" = Add([Id; 7]),
        "-" = Sub([Id; 7]),
        "*" = Mul([Id; 7]),
        "<<" = LeftShift([Id; 7]),
        ">>" = RightShift([Id; 7]),
        ">>>" = ArithmeticRightShift([Id; 7]),
        Symbol(ArithSymbol),
        Width(WidthInt),
        Signed(bool),
    }
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct ArithSymbol {
    pub name: StringRef,
    pub width: WidthInt,
}

impl FromStr for ArithSymbol {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

impl Display for ArithSymbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}:bv<{}>", self.name, self.width)
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
            Expr::BVSymbol { name, width } => out.add(Arith::Symbol(ArithSymbol { name, width })),
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
    let width_out = out.add(Arith::Width(width_out));
    let width_a = out.add(Arith::Width(width_a));
    let width_b = out.add(Arith::Width(width_b));
    let sign_a = out.add(Arith::Signed(sign_a));
    let sign_b = out.add(Arith::Signed(sign_b));
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
fn remove_ext(ctx: &Context, e: ExprRef) -> (ExprRef, bool) {
    match ctx[e] {
        Expr::BVZeroExt { e, .. } => (remove_ext(ctx, e).0, false),
        Expr::BVSignExt { e, .. } => (remove_ext(ctx, e).0, true),
        _ => (e, false),
    }
}

/// Convert from the arithmetic expression IR back to our internal SMTLib based IR.
pub fn from_arith(ctx: &mut Context, expr: &RecExpr<Arith>) -> ExprRef {
    let expressions = expr.as_ref();
    let mut todo = vec![(expressions.len() - 1, false)];
    let mut stack = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = &expressions[e];

        // Check if there are children that we need to compute first.
        if !bottom_up && !expr.children().is_empty() {
            todo.push((e, true));
            for child_id in expr.children() {
                todo.push((usize::from(*child_id), false));
            }
            continue;
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let result = match expr {
            Arith::Symbol(ArithSymbol { name, width }) => ctx.symbol(*name, Type::BV(*width)),
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
            Arith::Width(width) => ctx.bit_vec_val(*width, 32),
            Arith::Signed(is_minus) => ctx.bit_vec_val(*is_minus, 1),
        };
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

fn patronus_bin_op(
    ctx: &mut Context,
    stack: &mut Vec<ExprRef>,
    op: fn(&mut Context, ExprRef, ExprRef) -> ExprRef,
) -> ExprRef {
    let wo = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let wa = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sa = get_u64(ctx, stack.pop().unwrap()) != 0;
    let a = extend(ctx, stack.pop().unwrap(), wo, wa, sa);
    let wb = get_u64(ctx, stack.pop().unwrap()) as WidthInt;
    let sb = get_u64(ctx, stack.pop().unwrap()) != 0;
    let b = extend(ctx, stack.pop().unwrap(), wo, wb, sb);
    op(ctx, a, b)
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
    debug_assert_eq!(expr.get_bv_type(ctx).unwrap(), w_in);
    match w_out.cmp(&w_in) {
        Ordering::Less => unreachable!("cannot extend from {w_in} to {w_out}"),
        Ordering::Equal => expr,
        Ordering::Greater if !signed => ctx.zero_extend(expr, w_out - w_in),
        Ordering::Greater => ctx.sign_extend(expr, w_out - w_in),
    }
}

type EGraph = egg::EGraph<Arith, ()>;

fn create_rewrites() -> Vec<egg::Rewrite<Arith, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)" if commute_add_condition("?wo", "?wa", "?sa", "?wb", "?sb")),
    ]
}

fn commute_add_condition(
    wo: &'static str,
    wa: &'static str,
    sa: &'static str,
    wb: &'static str,
    sb: &'static str,
) -> impl Fn(&mut EGraph, egg::Id, &egg::Subst) -> bool {
    let wo = wo.parse().unwrap();
    let wa = wa.parse().unwrap();
    let sa = sa.parse().unwrap();
    let wb = wb.parse().unwrap();
    let sb = sb.parse().unwrap();
    move |egraph, _, subst| {
        let wo = get_width_from_e_graph(egraph, subst, wo);
        let wa = get_width_from_e_graph(egraph, subst, wa);
        let wb = get_width_from_e_graph(egraph, subst, wb);
        let sa = get_signed_from_e_graph(egraph, subst, sa);
        let sb = get_signed_from_e_graph(egraph, subst, sb);
        // actual condition
        wa == wb && wo >= wa
    }
}

fn get_width_from_e_graph(egraph: &mut EGraph, subst: &egg::Subst, v: Var) -> WidthInt {
    match egraph[subst[v]].nodes.as_slice() {
        [Arith::Width(w)] => *w,
        _ => unreachable!("expected a width!"),
    }
}

fn get_signed_from_e_graph(egraph: &mut EGraph, subst: &egg::Subst, v: Var) -> bool {
    match egraph[subst[v]].nodes.as_slice() {
        [Arith::Signed(s)] => *s,
        _ => unreachable!("expected a signed!"),
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
        let runner = egg::Runner::default()
            .with_expr(&egg_expr_in)
            .run(&create_rewrites());

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
