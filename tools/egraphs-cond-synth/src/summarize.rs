// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::samples::{RuleInfo, Samples};
use egg::Var;
use patronus::expr::WidthInt;
use rustc_hash::FxHashMap;

/// generate a simplified re-writ condition from samples, using BDDs
pub fn bdd_summarize(rule: &RuleInfo, samples: &Samples) {
    for (assignment, is_equal) in samples.iter() {
        let v = FxHashMap::from_iter(assignment);
    }
}

const FEATURES: &[Feature] = &[
    Feature {
        name: "is_unsigned", // (13)
        len: |r| Some(r.signs().count()),
        eval: |r, v, o| {
            for sign in r.signs() {
                // s_i == unsign
                o.push(v[&sign] == 0);
            }
        },
    },
    Feature {
        name: "is_width_equal", // (14)
        len: |r| {
            if r.widths().count() <= 0 {
                None
            } else {
                Some(r.widths().count() * (r.widths().count() - 1))
            }
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        // w_i == w_j
                        o.push(v[&w_i] == v[&w_j]);
                    }
                }
            }
        },
    },
    Feature {
        name: "is_width_smaller", // (15) + (16)
        len: |r| {
            if r.widths().count() <= 0 {
                None
            } else {
                Some(r.widths().count() * (r.widths().count() - 1) * 3)
            }
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        let (w_i, w_j) = (v[&w_i], v[&w_j]);
                        // w_i < w_j
                        o.push(w_i < w_j);
                        // w_i + 1 < w_j
                        o.push(w_i + 1 < w_j);
                        // w_i - 1 < w_j
                        o.push(w_i - 1 < w_j);
                    }
                }
            }
        },
    },
    Feature {
        name: "is_width_sum_smaller", // (17) + (18)
        len: |r| {
            if r.widths().count() <= 1 {
                None
            } else {
                Some(r.widths().count() * (r.widths().count() - 1) * (r.widths().count() - 2) * 2)
            }
        },
        eval: |r, v, o| {
            for w_i in r.widths() {
                for w_j in r.widths() {
                    if w_i != w_j {
                        for w_k in r.widths() {
                            if w_k != w_i && w_k != w_j {
                                let (w_i, w_j, w_k) = (v[&w_i], v[&w_j], v[&w_k]);
                                // w_i + w_j < w_k
                                o.push(w_i + w_j < w_k);
                                // w_i + 2**w_j < w_k
                                o.push(w_i as u64 + 2u64.pow(w_j) < w_k as u64);
                            }
                        }
                    }
                }
            }
        },
    },
];

struct Feature {
    name: &'static str,
    len: fn(rule: &RuleInfo) -> Option<usize>,
    eval: fn(rule: &RuleInfo, v: &FxHashMap<Var, WidthInt>, out: &mut Vec<bool>),
}
