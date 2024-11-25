// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::analysis::analyze_for_serialization;
use super::TransitionSystem;
use crate::expr::{
    serialize_expr, serialize_expr_ref, Context, ExprRef, SerializableIrNode, TypeCheck,
};
use std::io::Write;

fn serialize_transition_system<W: Write>(
    ctx: &Context,
    sys: &TransitionSystem,
    writer: &mut W,
) -> std::io::Result<()> {
    if !sys.name.is_empty() {
        writeln!(writer, "{}", sys.name)?;
    }

    let signals = analyze_for_serialization(ctx, sys, true).signal_order;
    let max_id = signals
        .iter()
        .map(|s| s.expr.index())
        .max()
        .unwrap_or_default();
    let mut names = vec![None; max_id + 1];
    for root in signals.iter() {
        // try names in this order:
        // - symbol name
        // - signal name
        // - %{id}
        let name = ctx
            .get_symbol_name(root.expr)
            .map(|n| n.to_string())
            .unwrap_or_else(|| {
                sys.names[root.expr]
                    .map(|n| ctx.get_str(n).to_string())
                    .unwrap_or(format!("%{}", root.expr.index()))
            });
        names[root.expr.index()] = Some(name);
    }

    // this closure allows us to use node names instead of serializing all sub-expressions
    let serialize_child = |expr_ref: &ExprRef, writer: &mut W| -> std::io::Result<bool> {
        if let Some(Some(name)) = names.get(expr_ref.index()) {
            write!(writer, "{}", name)?;
            Ok(false)
        } else {
            Ok(true) // recurse to child
        }
    };

    // signals
    let mut aliases = Vec::new();
    for root in signals.iter() {
        let maybe_info = sys.get_signal(root.expr);
        let name = names[root.expr.index()].as_ref().unwrap();
        let expr = ctx.get(root.expr);

        // print the kind and name
        let kind = find_type(maybe_info, &mut aliases);
        write!(writer, "{} {}", kind, name)?;

        // print the type
        let tpe = expr.get_type(ctx);
        write!(writer, " : {tpe}",)?;

        if expr.is_symbol() && expr.get_symbol_name(ctx).unwrap() == name {
            writeln!(writer)?;
        } else {
            write!(writer, " = ")?;
            serialize_expr(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }

        // print aliases
        for alias in aliases.iter() {
            // for aliases, we prefer the signal name
            // this allows us to e.g. print the name of an output which is also an input correctly
            let alias_name = maybe_info
                .unwrap()
                .name
                .map(|n| ctx.get_str(n))
                .unwrap_or(name);
            writeln!(writer, "{alias} {alias_name} : {tpe} = {name}")?;
        }
    }

    // states
    for state in sys.states.iter() {
        let name = ctx
            .get_symbol_name(state.symbol)
            .expect("all states are required to have a name!");
        let tpe = state.symbol.get_type(ctx);
        writeln!(writer, "state {name} : {tpe}")?;

        if let Some(expr) = &state.init {
            write!(writer, "  [init] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
        if let Some(expr) = &state.next {
            write!(writer, "  [next] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
    }

    Ok(())
}

impl SerializableIrNode for TransitionSystem {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_transition_system(ctx, self, writer)
    }
}
