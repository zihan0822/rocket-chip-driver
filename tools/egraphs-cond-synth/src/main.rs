// Copyright 2024 Cornell University
// Copyright 2024 Princeton University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

mod samples;
mod summarize;

use crate::summarize::bdd_summarize;
use clap::Parser;
use egg::*;
use patronus::expr::*;
use patronus_egraphs::*;

#[derive(Parser, Debug)]
#[command(name = "patronus-egraphs-cond-synth")]
#[command(version)]
#[command(about = "Synthesizes rewrite conditions..", long_about = None)]
struct Args {
    #[arg(long, default_value = "8")]
    max_width: WidthInt,
    #[arg(long)]
    print_samples: bool,
    #[arg(long)]
    dump_smt: bool,
    #[arg(long)]
    bdd_formula: bool,
    #[arg(
        long,
        help = "checks the current condition, prints out if it disagrees with the examples we generate"
    )]
    check_cond: bool,
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

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

fn create_rewrites() -> Vec<Rewrite<Arith, ()>> {
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

fn main() {
    let args = Args::parse();

    // remember start time
    let start = std::time::Instant::now();

    // find rule and extract both sides
    let rewrites = create_rewrites();
    let rule = match rewrites.iter().find(|r| r.name.as_str() == args.rule) {
        Some(r) => r,
        None => {
            let available = rewrites.iter().map(|r| r.name.as_str()).collect::<Vec<_>>();
            panic!(
                "Failed to find rewrite rule `{}`!\nAvailable rules are: {:?}",
                args.rule, available
            );
        }
    };

    let (samples, rule_info) = samples::generate_samples(
        &args.rule,
        rule,
        args.max_width,
        true,
        args.dump_smt,
        args.check_cond,
    );
    let delta_t = std::time::Instant::now() - start;

    println!("Found {} equivalent rewrites.", samples.num_equivalent());
    println!(
        "Found {} unequivalent rewrites.",
        samples.num_unequivalent()
    );
    println!(
        "Took {delta_t:?} on {} threads.",
        rayon::current_num_threads()
    );

    if args.print_samples {
        for sample in samples.iter() {
            println!("{:?}", sample);
        }
    }

    if args.bdd_formula {
        let summarize_start = std::time::Instant::now();
        let formula = bdd_summarize(&rule_info, &samples);
        let summarize_delta_t = std::time::Instant::now() - summarize_start;
        println!("Generated formula in {summarize_delta_t:?}:\n{}", formula);
    }
}
