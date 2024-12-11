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

pub struct ArithRewrite {
    name: String,
    /// most general lhs pattern
    lhs: Pattern<Arith>,
    /// rhs pattern with all widths derived from the lhs, maybe be the same as rhs
    rhs_derived: Pattern<Arith>,
    /// variables use by the condition
    cond_vars: Vec<String>,
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
            .map(|n| n.as_ref().to_string())
            .collect();
        Self {
            name: name.to_string(),
            lhs: lhs.parse::<_>().unwrap(),
            rhs_derived: rhs_derived.parse::<_>().unwrap(),
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
            let vars: Vec<Var> = self.cond_vars.iter().map(|n| n.parse().unwrap()).collect();
            let condition = move |egraph: &mut EGraph, _, subst: &Subst| {
                let values: Vec<WidthInt> = vars
                    .iter()
                    .map(|v| get_width_from_e_graph(egraph, subst, *v))
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
}

pub fn create_rewrites() -> Vec<ArithRewrite> {
    vec![
        arith_rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
        arith_rewrite!("merge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            "(<< ?wo ?wab ?sab (<< ?wab ?wa ?sa ?a ?wb 0 ?b) ?wc 0 ?c)" =>
            // note: in this version we set the width of (b + c) on the RHS to be the width of the
            //       result (w_o)
            "(<< ?wo ?wa ?sa ?a ?wo 0 (+ ?wo ?wb 0 ?b ?wc 0 ?c))";
            if["?wo", "?wa", "?sa", "?wb", "?wc"], |w| w[1] == w[2] && w[0] >= w[1]),
    ]
}

type EGraph = egg::EGraph<Arith, ()>;

fn get_width_from_e_graph(egraph: &EGraph, subst: &Subst, v: Var) -> WidthInt {
    egraph[subst[v]]
        .nodes
        .iter()
        .flat_map(|n| {
            if let Arith::WidthConst(w) = n {
                Some(*w)
            } else {
                None
            }
        })
        .next()
        .expect("failed to find constant width")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_egg() {
        let egg_rewrites = create_rewrites()
            .into_iter()
            .map(|r| r.to_egg())
            .reduce(|mut a, mut b| {
                a.append(&mut b);
                a
            })
            .unwrap();
        assert_eq!(egg_rewrites.len(), 2);
    }
}
