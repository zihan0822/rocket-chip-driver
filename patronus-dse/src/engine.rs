// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::Context;
use patronus::system::TransitionSystem;

/// Symbolic execution engine.
pub struct SymEngine {
    #[allow(dead_code)]
    sys: TransitionSystem,
}

impl SymEngine {
    pub fn new(_ctx: &Context, sys: TransitionSystem) -> Self {
        Self { sys }
    }
}
