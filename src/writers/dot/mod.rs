// SPDX-License-Identifier: MIT OR Apache-2.0

//! Renders the lemma dependency trees (see [`crate::theorem::Claim`]) of every
//! oracle in an `equivalence`/`hybrid` game hop as a single Graphviz DOT
//! digraph, so it can be piped straight into `dot`/`neato`/etc.

use std::collections::BTreeSet;
use std::fmt::Write;

use crate::theorem::{Claim, ClaimType};

/// Claim names domino gives a built-in meaning to: `no-abort` is derived
/// automatically (whenever `equal-aborts` holds), and `equal-aborts`,
/// `same-output`, `invariant` are the three proof obligations every oracle
/// is checked against (injected with default dependencies unless the
/// theorem overrides them). They aren't "just another lemma" the author
/// wrote, so they're called out separately in the graph.
const BUILTIN_CLAIM_NAMES: [&str; 4] = ["no-abort", "invariant", "same-output", "equal-aborts"];

fn is_builtin_claim_name(name: &str) -> bool {
    BUILTIN_CLAIM_NAMES.contains(&name)
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn claim_fillcolor(ty: ClaimType) -> &'static str {
    match ty {
        ClaimType::Lemma => "lightblue",
        ClaimType::Relation => "lightyellow",
        ClaimType::Invariant => "lightgreen",
        ClaimType::LeftPackageInvariant | ClaimType::RightPackageInvariant => "orange",
        ClaimType::LeftGameInvariant | ClaimType::RightGameInvariant => "plum",
        ClaimType::InitialState => "lightgreen",
    }
}

/// Writes the nodes and edges for one oracle's claim tree. `id_prefix` is
/// prepended to every node id (but not its label) so that same-named claims
/// (`same-output`, `no-abort`, ...) from different oracles don't collapse
/// into the same DOT node once multiple trees share a graph/cluster.
fn write_claim_tree_body(out: &mut String, id_prefix: &str, tree: &[Claim]) {
    let node_id = |name: &str| escape(&format!("{id_prefix}{name}"));

    let known: BTreeSet<&str> = tree.iter().map(Claim::name).collect();

    for claim in tree {
        let id = node_id(claim.name());
        let builtin = is_builtin_claim_name(claim.name());
        let fillcolor = if builtin {
            "lightgray"
        } else {
            claim_fillcolor(claim.ty())
        };
        let (style, extra) = if claim.is_admitted() {
            ("filled,dashed", ", color=red")
        } else if builtin {
            ("filled,dotted", "")
        } else {
            ("filled", "")
        };

        let mut annotations = Vec::new();
        if builtin {
            annotations.push("builtin");
        }
        if claim.is_admitted() {
            annotations.push("admitted");
        }
        let label = if annotations.is_empty() {
            escape(claim.name())
        } else {
            format!("{}\\n({})", escape(claim.name()), annotations.join(", "))
        };

        writeln!(
            out,
            "  \"{id}\" [label=\"{label}\", shape=box, style=\"{style}\", fillcolor={fillcolor}{extra}];",
        )
        .unwrap();
    }

    // Dependencies referenced by name but never given their own `lemmas`
    // entry (most commonly the built-in `no-abort`) still get a node, so the
    // graph stays connected and it's clear they're implicit.
    let mut implicit: Vec<&str> = tree
        .iter()
        .flat_map(Claim::dependencies)
        .map(String::as_str)
        .filter(|dep| !known.contains(dep))
        .collect();
    implicit.sort_unstable();
    implicit.dedup();

    for dep in implicit {
        let id = node_id(dep);
        let label = escape(dep);
        let suffix = if is_builtin_claim_name(dep) {
            "builtin"
        } else {
            "undeclared"
        };
        writeln!(
            out,
            "  \"{id}\" [label=\"{label}\\n({suffix})\", shape=ellipse, style=\"filled,dotted\", fillcolor=lightgray];",
        )
        .unwrap();
    }

    for claim in tree {
        for dep in claim.dependencies() {
            writeln!(
                out,
                "  \"{}\" -> \"{}\";",
                node_id(claim.name()),
                node_id(dep)
            )
            .unwrap();
        }
    }
}

/// Renders the lemma dependency trees of every oracle of an
/// `equivalence`/`hybrid` game hop into a single DOT digraph, one cluster
/// subgraph per oracle.
///
/// Edges point from a claim to the claims it depends on (i.e. from goal to
/// hint), so with graphviz's default top-to-bottom layout the final proof
/// obligations (`same-output`, `equal-aborts`, `invariant`, ...) end up on
/// top of each cluster and the leaves (e.g. `no-abort`) at the bottom.
pub fn lemma_dependency_dot(
    graph_name: &str,
    label: &str,
    trees: &[(String, Vec<Claim>)],
) -> String {
    let mut out = String::new();

    writeln!(out, "digraph \"{}\" {{", escape(graph_name)).unwrap();
    writeln!(out, "  labelloc=\"t\";").unwrap();
    writeln!(out, "  label=\"{}\";", escape(label)).unwrap();
    writeln!(out, "  node [style=filled, fontname=\"monospace\"];").unwrap();

    for (oracle_name, tree) in trees {
        writeln!(out).unwrap();
        writeln!(out, "  subgraph \"cluster_{}\" {{", escape(oracle_name)).unwrap();
        writeln!(out, "    label=\"{}\";", escape(oracle_name)).unwrap();
        writeln!(out, "    style=dashed;").unwrap();

        write_claim_tree_body(&mut out, &format!("{oracle_name}::"), tree);

        writeln!(out, "  }}").unwrap();
    }

    writeln!(out, "}}").unwrap();
    out
}
