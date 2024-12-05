// Copyright 2024 Cornell University
// Copyright 2024 Princeton University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Amelia Dobis <amelia.dobis@princeton.edu>
// author: Mohanna Shahrad <mohanna@princeton.edu>

mod samples;

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
    #[arg(value_name = "RULE", index = 1)]
    rule: String,
}

fn create_rewrites() -> Vec<Rewrite<Arith, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?wo ?wa ?sa ?a ?wb ?sb ?b)" => "(+ ?wo ?wb ?sb ?b ?wa ?sa ?a)"),
    ]
}

fn main() {
    let args = Args::parse();

    // find rule and extract both sides
    let rewrites = create_rewrites();
    let rule = rewrites
        .iter()
        .find(|r| r.name.as_str() == args.rule)
        .unwrap_or_else(|| panic!("Failed to find rewrite rule `{}`!", args.rule));

    let samples = samples::generate_samples(&args.rule, rule, args.max_width);
    println!("Found {} equivalent rewrites.", samples.num_equivalent());
    println!(
        "Found {} unequivalent rewrites.",
        samples.num_unequivalent()
    );
}
