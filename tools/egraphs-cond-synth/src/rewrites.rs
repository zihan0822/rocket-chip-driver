// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use egg::*;
use patronus::expr::*;
use patronus_egraphs::*;

/// our version of the egg re-write macro
macro_rules! arith_rewrite {
    (
        $name:expr;
        $lhs:expr => $rhs:expr;
        if $cond:expr
    ) => {{
        ArithRewrite::new($name, $lhs, $rhs)
    }};
}

struct ArithRewrite {
    name: String,
    lhs: Pattern<Arith>,
    rhs: Pattern<Arith>,
}

impl ArithRewrite {
    fn new(name: &str, lhs: &str, rhs: &str) -> Self {
        Self {
            name: name.to_string(),
            lhs: lhs.parse::<_>().unwrap(),
            rhs: rhs.parse::<_>().unwrap(),
        }
    }

    fn to_egg(&self) -> Rewrite<Arith, ()> {
        Rewrite::new(self.name.clone(), self.lhs.clone(), self.rhs.clone()).unwrap()
    }
}

pub fn create_rewrites() -> Vec<Rewrite<Arith, ()>> {
    let rewrites = vec![
        arith_rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"; if true),
        arith_rewrite!("merge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            "(<< ?wo ?wab ?sab (<< ?wab ?wa ?sa ?a ?wb 0 ?b) ?wc 0 ?c)" =>
            // note: in this version we set the width of (b + c) on the RHS to be the width of the
            //       result (w_o)
            "(<< ?wo ?wa ?sa ?a ?wo 0 (+ ?wo ?wb 0 ?b ?wc 0 ?c))"; if merge_left_shift_cond("?wo", "?wa", "?sa", "?wb", "?wc")),
    ];
    rewrites.into_iter().map(|r| r.to_egg()).collect()
}

type EGraph = egg::EGraph<Arith, ()>;

fn merge_left_shift_cond(
    wo: &'static str,
    wa: &'static str,
    sa: &'static str,
    wb: &'static str,
    wc: &'static str,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let wo = wo.parse().unwrap();
    let wa = wa.parse().unwrap();
    let sa = sa.parse().unwrap();
    let wb = wb.parse().unwrap();
    let wc = wc.parse().unwrap();
    move |egraph, _, subst| {
        let wo = get_width_from_e_graph(egraph, subst, wo);
        let wa = get_width_from_e_graph(egraph, subst, wa);
        let sa = get_width_from_e_graph(egraph, subst, sa);
        let wb = get_width_from_e_graph(egraph, subst, wb);
        let wc = get_width_from_e_graph(egraph, subst, wc);
        // actual condition
        wa == wb && wo >= wa
    }
}

fn get_width_from_e_graph(egraph: &mut EGraph, subst: &Subst, v: Var) -> WidthInt {
    match egraph[subst[v]].nodes.as_slice() {
        [Arith::WidthConst(w)] => *w,
        _ => unreachable!("expected a width!"),
    }
}
