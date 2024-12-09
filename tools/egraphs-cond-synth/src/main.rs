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
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

fn create_rewrites() -> Vec<Rewrite<Arith, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
        rewrite!("merge-left-shift";
            // we require that b, c and (b + c) are all unsigned
            "(<< ?wo ?wab ?sab (<< ?wab ?wa ?sa ?a ?wb 0 ?b) ?wc 0 ?c)" =>
            // note: in this version we set the width of (b + c) on the RHS to be the width of the
            //       result (w_o)
            "(<< ?wo ?wa ?sa ?a ?wo 0 (+ ?wo ?wb 0 ?b ?wc 0 ?c))"),
    ]
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

    let (samples, rule_info) =
        samples::generate_samples(&args.rule, rule, args.max_width, true, args.dump_smt);
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
