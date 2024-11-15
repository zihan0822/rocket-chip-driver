// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::ExprRef;
use baa::{BitVecValue, BitVecValueRef};

/// An implementation of a transition system simulator.
pub trait Simulator {
    type SnapshotId;

    /// Initializes all states and inputs to zero.
    fn init(&mut self);

    /// Recalculate signals.
    fn update(&mut self);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator.
    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>);

    /// Inspect the value of any bit vector expression in the circuit
    fn get(&self, expr: ExprRef) -> Option<BitVecValue>;

    /// Retrieve the value of an array element
    fn get_element<'a>(
        &self,
        expr: ExprRef,
        index: impl Into<BitVecValueRef<'a>>,
    ) -> Option<BitVecValue>;

    fn step_count(&self) -> u64;

    /// Takes a snapshot of the state (excluding inputs) and saves it internally.
    fn take_snapshot(&mut self) -> Self::SnapshotId;
    /// Restores a snapshot that was previously taken with the same simulator.
    fn restore_snapshot(&mut self, id: Self::SnapshotId);
}
