// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
// some of the code is based on `egg` source code which is licenced under MIT

use crate::{get_const_width_or_sign, is_bin_op, EGraph};
use egg::Language;
use rustc_hash::FxHashMap;
use std::io::Write;

pub fn to_pdf(filename: &str, egraph: &EGraph) -> std::io::Result<()> {
    use std::process::{Command, Stdio};
    let mut child = Command::new("dot")
        .args(["-Tpdf", "-o", filename])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .spawn()?;
    let stdin = child.stdin.as_mut().expect("Failed to open stdin");
    write_to_dot(stdin, egraph)?;
    match child.wait()?.code() {
        Some(0) => Ok(()),
        Some(e) => panic!("dot program returned error code {}", e),
        None => panic!("dot program was killed by a signal"),
    }
}

/// Reimplements egg's `to_dot` functionality.
/// This is necessary because we do not want to show the Width nodes in the graph, because
/// otherwise it becomes very confusing.
pub fn write_to_dot(out: &mut impl Write, egraph: &EGraph) -> std::io::Result<()> {
    writeln!(out, "digraph egraph {{")?;

    // set compound=true to enable edges to clusters
    writeln!(out, "  compound=true")?;
    writeln!(out, "  clusterrank=local")?;

    // create a map from e-class id to width
    let widths = FxHashMap::from_iter(
        egraph
            .classes()
            .flat_map(|class| get_const_width_or_sign(egraph, class.id).map(|w| (class.id, w))),
    );

    // define all the nodes, clustered by eclass
    for class in egraph.classes() {
        if !widths.contains_key(&class.id) {
            writeln!(out, "  subgraph cluster_{} {{", class.id)?;
            writeln!(out, "    style=dotted")?;
            for (i, node) in class.iter().enumerate() {
                writeln!(out, "    {}.{}[label = \"{}\"]", class.id, i, node)?;
            }
            writeln!(out, "  }}")?;
        }
    }

    for class in egraph.classes() {
        if !widths.contains_key(&class.id) {
            for (i_in_class, node) in class.iter().enumerate() {
                let nodes_and_labels = if is_bin_op(node) {
                    // w, w_a, s_a, a, w_b, s_b, b
                    let cc = node.children();
                    let w_a = widths[&cc[1]];
                    let s_a = widths[&cc[2]];
                    let a = cc[3];
                    let w_b = widths[&cc[4]];
                    let s_b = widths[&cc[5]];
                    let b = cc[6];
                    vec![
                        (a, format!("{w_a}{}", if s_a == 0 { "" } else { "s" })),
                        (b, format!("{w_b}{}", if s_b == 0 { "" } else { "s" })),
                    ]
                } else {
                    assert_eq!(node.len(), 0);
                    vec![]
                };
                for (child, label) in nodes_and_labels.into_iter() {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let anchor = "";
                    let child_leader = egraph.find(child);
                    if child_leader == class.id {
                        writeln!(
                            out,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.{}:n [lhead = cluster_{}, label=\"{}\"]",
                            class.id, i_in_class, anchor, class.id, i_in_class, class.id, label
                        )?;
                    } else {
                        writeln!(
                            out,
                            // {}.0 to pick an arbitrary node in the cluster
                            "  {}.{}{} -> {}.0 [lhead = cluster_{}, label=\"{}\"]",
                            class.id, i_in_class, anchor, child, child_leader, label
                        )?;
                    }
                }
            }
        }
    }

    write!(out, "}}")
}
