// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::Context;
use crate::system::TransitionSystem;

/// Symbolic execution engine.
pub struct SymEngine {
    sys: TransitionSystem,
}

impl SymEngine {
    pub fn new(_ctx: &Context, sys: TransitionSystem) -> Self {
        Self { sys }
    }
}
