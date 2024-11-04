// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use boolean_expression::{BDDFunc, BDD};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct GuardCtx {
    bdd: BDD<u16>,
}

impl Default for GuardCtx {
    fn default() -> Self {
        let bdd = BDD::new();
        Self { bdd }
    }
}

impl GuardCtx {
    pub fn tru(&mut self) -> Guard {
        self.bdd.constant(true)
    }

    pub fn and(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.and(a, b)
    }

    pub fn or(&mut self, a: Guard, b: Guard) -> Guard {
        self.bdd.or(a, b)
    }

    pub fn not(&mut self, e: Guard) -> Guard {
        self.bdd.not(e)
    }

    /// guard can never be true
    pub fn is_false(&self, e: Guard) -> bool {
        matches!(e, boolean_expression::BDD_ZERO)
    }

    pub fn is_true(&self, e: Guard) -> bool {
        matches!(e, boolean_expression::BDD_ONE)
    }
}

type Guard = BDDFunc;

/// Value in a `[[ValueSummary]]`.
pub trait Value: Clone + Eq + Hash {
    type Context;

    /// Indicates that the value is trivially true.
    fn is_true(&self, _ec: &Self::Context) -> bool {
        false
    }
    /// Indicates that the value is trivially false.
    fn is_false(&self, _ec: &Self::Context) -> bool {
        false
    }
}

#[allow(dead_code)]
pub struct ValueSummary<V: Value> {
    entries: Vec<Entry<V>>,
}

impl<V: Value> ValueSummary<V> {
    pub fn new(gc: &mut GuardCtx, value: V) -> Self {
        Self {
            entries: vec![Entry {
                guard: gc.tru(),
                value,
            }],
        }
    }

    /// Applies an operation to a and b.
    pub fn apply_bin_op(
        ec: &mut V::Context,
        gc: &mut GuardCtx,
        op: fn(ec: &mut V::Context, a: V, b: V) -> V,
        a: Self,
        b: Self,
    ) -> Self {
        let mut a = a.entries;
        let mut b = b.entries;
        debug_assert!(!a.is_empty() && !b.is_empty());
        let mut out = Vec::with_capacity(a.len() + b.len());

        // first we check to see if any guards are the same, then we do not need to apply the cross product
        let a_guards: HashSet<Guard> = a.iter().map(|e| e.guard).collect();
        let b_guards: HashSet<Guard> = b.iter().map(|e| e.guard).collect();
        let common_guards: HashSet<Guard> = a_guards.intersection(&b_guards).cloned().collect();

        if !common_guards.is_empty() {
            // merge common guard entries
            let mut sorted_common_guards: Vec<Guard> = common_guards.iter().cloned().collect();
            sorted_common_guards.sort();
            for guard in sorted_common_guards.into_iter() {
                // unwrap should never fail, since otherwise this would not be a common guard!
                let a_expr = a.iter().find(|e| e.guard == guard).cloned().unwrap().value;
                let b_expr = b.iter().find(|e| e.guard == guard).cloned().unwrap().value;

                // we can create exactly one new entry with the common guard
                out.push(Entry {
                    guard,
                    value: op(ec, a_expr, b_expr),
                })
            }

            // remove any entries that we already processed
            a.retain(|e| !common_guards.contains(&e.guard));
            b.retain(|e| !common_guards.contains(&e.guard));
        }

        // for any other guards, we need to consider all possible combinations
        if !a.is_empty() {
            debug_assert!(!b.is_empty(), "when a is empty, b should also be empty!");

            for a_entry in a.into_iter() {
                for b_entry in b.iter() {
                    let guard = gc.and(a_entry.guard, b_entry.guard);
                    if !gc.is_false(guard) {
                        // create a new entry
                        out.push(Entry {
                            guard,
                            value: op(ec, a_entry.value.clone(), b_entry.value.clone()),
                        })
                    }
                }
            }
        }

        Self { entries: out }
    }

    /// Indicates that this value summary is trivially true.
    fn is_true(&self, ec: &V::Context) -> bool {
        match self.entries.as_slice() {
            [entry] => entry.value.is_true(ec),
            _ => false,
        }
    }

    /// Indicates that this value summary is trivially false.
    fn is_false(&self, ec: &V::Context) -> bool {
        match self.entries.as_slice() {
            [entry] => entry.value.is_false(ec),
            _ => false,
        }
    }

    /// Returns the number of entries in the value summary.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// combines entries with the same value into one
    fn coalesce(&mut self, gc: &mut GuardCtx) {
        let mut by_value = HashMap::with_capacity(self.entries.len());
        let mut delete_list = vec![];
        for ii in 0..self.entries.len() {
            let entry = self.entries[ii].clone();
            if let Some(prev_ii) = by_value.get(&entry.value) {
                // we found a duplicate! let's merge
                let prev_ii: usize = *prev_ii;
                let prev = self.entries[prev_ii].clone();
                let combined_guard = gc.or(prev.guard, entry.guard);
                // update the current entry
                self.entries[ii].guard = combined_guard;
                // schedule the duplicate to be deleted
                delete_list.push(prev_ii);
            }
            // remember the final entry containing this value
            by_value.insert(entry.value, ii);
        }

        // delete duplicate entries
        delete_entries(delete_list, &mut self.entries);
    }
}

impl<V: Value + ToGuard> ValueSummary<V> {
    /// Combines two values depending on a conditional.
    pub fn apply_ite(
        ec: &mut V::Context,
        gc: &mut GuardCtx,
        cond: Self,
        tru: Self,
        fals: Self,
    ) -> Self {
        // is the condition trivially true?
        if cond.is_true(ec) {
            return tru;
        }
        if cond.is_false(ec) {
            return fals;
        }

        // lift condition values into a single guard
        let tru_cond = cond.to_guard(ec, gc);
        let fals_cond = gc.not(tru_cond);
        if gc.is_true(tru_cond) {
            return tru;
        }
        if gc.is_true(fals_cond) {
            return fals;
        }

        // create combined entries
        let mut entries = Vec::with_capacity(tru.len() + fals.len());
        for e in tru.entries.into_iter() {
            entries.push(Entry {
                guard: gc.and(e.guard, tru_cond),
                value: e.value,
            });
        }
        for e in fals.entries.into_iter() {
            entries.push(Entry {
                guard: gc.and(e.guard, fals_cond),
                value: e.value,
            });
        }

        // return combined value summary
        ValueSummary { entries }
    }

    /// Converts the value summary into a guard.
    fn to_guard(&self, ec: &mut V::Context, gc: &mut GuardCtx) -> Guard {
        match self.entries.as_slice() {
            [] => unreachable!("value summaries should always have at least one entry"),
            [one] => {
                debug_assert!(
                    gc.is_true(one.guard),
                    "with a single entry, guard needs to be true"
                );
                one.value.to_guard(ec, gc).expect("should be bool")
            }
            entries => entries
                .iter()
                .map(|e| {
                    let value_as_guard = e.value.to_guard(ec, gc).expect("should be bool");
                    gc.and(e.guard, value_as_guard)
                })
                .collect::<Vec<_>>()
                .into_iter()
                .reduce(|a, b| gc.or(a, b))
                .unwrap(),
        }
    }

    /// Canonicalizes a boolean value summary such that it only contains two or fewer entries.
    pub fn import_into_guard(&mut self, ec: &mut V::Context, gc: &mut GuardCtx) {
        let value_as_guard = self.to_guard(ec, gc);
        if gc.is_true(value_as_guard) {
            self.entries = vec![Entry {
                guard: gc.tru(),
                value: V::true_value(ec),
            }];
            return;
        }
        if gc.is_false(value_as_guard) {
            self.entries = vec![Entry {
                guard: gc.tru(),
                value: V::false_value(ec),
            }];
            return;
        }
        self.entries = vec![
            Entry {
                guard: gc.not(value_as_guard),
                value: V::false_value(ec),
            },
            Entry {
                guard: value_as_guard,
                value: V::true_value(ec),
            },
        ];
    }
}

fn delete_entries<T>(delete_list: Vec<usize>, entries: &mut Vec<T>) {
    if !delete_list.is_empty() {
        let mut delete_iter = delete_list.into_iter().peekable();
        let mut index = 0usize;
        entries.retain(|_| {
            let current_index = index;
            index += 1;
            if delete_iter.peek().cloned() == Some(current_index) {
                delete_iter.next().unwrap();
                false
            } else {
                true
            }
        })
    }
}

/// Implemented by values that can be lifted into a guard.
pub trait ToGuard: Value {
    /// Indicates whether the given value can be turned into a guard.
    fn can_be_guard(&self, ec: &Self::Context) -> bool;

    /// Turns the value into a guard.
    fn to_guard(&self, ec: &Self::Context, gc: &mut GuardCtx) -> Option<Guard>;
    fn true_value(ec: &mut Self::Context) -> Self;
    fn false_value(ec: &mut Self::Context) -> Self;
}

impl Value for ExprRef {
    type Context = Context;

    fn is_true(&self, ec: &Context) -> bool {
        ec.get(*self).is_true()
    }

    fn is_false(&self, ec: &Context) -> bool {
        ec.get(*self).is_false()
    }
}

impl ToGuard for ExprRef {
    fn can_be_guard(&self, ec: &Self::Context) -> bool {
        ec.get(*self).get_bv_type(ec) == Some(1)
    }

    fn true_value(ec: &mut Self::Context) -> Self {
        ec.tru()
    }
    fn false_value(ec: &mut Self::Context) -> Self {
        ec.fals()
    }

    fn to_guard(&self, ec: &Context, gc: &mut GuardCtx) -> Option<Guard> {
        todo!()
    }
}

#[derive(Clone)]
struct Entry<V: Clone> {
    guard: Guard,
    value: V,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_value_summaries() {
        let mut ctx = Context::default();
        let mut gc = GuardCtx::default();

        let vs = ValueSummary::new(&mut gc, ctx.bv_symbol("a", 16));
        assert_eq!(vs.len(), 1);
    }

    #[test]
    fn test_delete_entries() {
        let mut entries = vec!['a', 'b', 'c', 'd'];
        delete_entries(vec![1, 2], &mut entries);
        assert_eq!(entries, ['a', 'd']);
    }
}
