// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::features::apply_features;
use crate::samples::{RuleInfo, Samples};

/// generate a simplified re-write condition from samples, using BDDs
pub fn bdd_summarize(rule: &RuleInfo, samples: &Samples) -> String {
    let results = apply_features(rule, samples);

    // generate BDD terminals
    let mut bdd = boolean_expression::BDD::<String>::new();
    let vars: Vec<_> = results
        .labels()
        .iter()
        .map(|ii| bdd.terminal(ii.clone()))
        .collect();

    println!("There are {} features", results.num_features());

    // start condition as trivially `false`
    let mut cond = boolean_expression::BDD_ZERO;
    for (features, is_equal) in results.iter() {
        let lits = features
            .into_iter()
            .enumerate()
            .map(|(terminal, is_true)| {
                if *is_true {
                    vars[terminal]
                } else {
                    bdd.not(vars[terminal])
                }
            })
            .collect::<Vec<_>>();
        let term = lits.into_iter().reduce(|a, b| bdd.and(a, b)).unwrap();
        let term = if is_equal { term } else { bdd.not(term) };

        cond = bdd.or(cond, term);
    }

    // extract simplified expression
    format!("{:?}", bdd.to_expr(cond))
}
