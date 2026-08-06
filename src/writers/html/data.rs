// SPDX-License-Identifier: MIT OR Apache-2.0

//! The graph data embedded in the generated HTML page, plus a small
//! hand-rolled JSON writer (the project has no `serde_json` dependency, and
//! this shape is simple enough not to need one -- see `json_string`/the
//! `write_json` methods below; the embedding is round-trip-tested against a
//! real `JSON.parse` in the headless-browser e2e checks, not just eyeballed).

use std::fmt::Write;

#[derive(Clone)]
pub struct NodeData {
    /// DOM/JS id, unique across the whole page (`{oracle}::{claim_name}`) for
    /// a main-graph node, or a freshly synthesized `flow-N` id for an
    /// invariant-flow node (which may re-embed the same underlying claim
    /// more than once -- see [`crate::writers::html::build_invariant_flow_graph`]).
    pub id: String,
    /// Bare claim name, for the label and the detail panel title.
    pub name: String,
    pub x: f64,
    pub y: f64,
    pub width: f64,
    pub height: f64,
    pub fill_color: &'static str,
    pub claim_type: &'static str,
    pub builtin: bool,
    pub admitted: bool,
    /// `None` for nodes where the distinction doesn't apply (state
    /// relations are always old-state-only structurally; implicit/undeclared
    /// stub nodes have no body to inspect at all).
    pub depends_on_new_state: Option<bool>,
    /// `true` for a dependency that's referenced by name but never given its
    /// own `lemmas {}` entry in this oracle (mirrors the dot writer's
    /// "(builtin)"/"(undeclared)" ellipse nodes).
    pub implicit: bool,
    pub domino_source: Option<String>,
    pub easycrypt_source: Option<String>,
    /// Other captured definitions (helper functions, or other
    /// lemmas/relations) that this claim's body calls, so a reviewer doesn't
    /// have to go hunting for them separately.
    pub referenced_definitions: Vec<ReferencedDefinition>,
}

#[derive(Clone)]
pub struct ReferencedDefinition {
    pub name: String,
    pub kind_label: &'static str,
    pub domino_source: String,
    pub easycrypt_source: String,
}

/// What relation an [`EdgeData`] draws between two nodes -- lets the JS side
/// style each kind distinctly instead of everything being a plain proof
/// dependency, and lets [`crate::writers::html::mod`]'s invariant-flow
/// builder tell a normal in-cluster dependency edge apart from a cross-oracle
/// jump/back-edge without re-deriving it from node shapes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    /// A claim's ordinary `lemmas { name: [dep, ...] }` hint, or an
    /// HTML-only helper-function call edge (see `find_function_calls`).
    Dependency,
    /// An explicit `with invariants [...]` scope entry: the claim assumes
    /// only this named invariant fragment on the old state, instead of the
    /// full (AND-of-every-fragment) `invariant`.
    WithInvariants,
    /// Invariant-flow view only: a fragment's establishment jumps into a
    /// freshly expanded cluster for another oracle that also declares it.
    CrossOracle,
    /// Invariant-flow view only: the jump target is already an ancestor of
    /// itself on the current expansion path (a cycle, e.g. a fragment
    /// depending on itself holding in the old state) -- points back at the
    /// existing ancestor node instead of expanding it again.
    Back,
}

impl EdgeKind {
    fn as_str(self) -> &'static str {
        match self {
            EdgeKind::Dependency => "dependency",
            EdgeKind::WithInvariants => "with-invariants",
            EdgeKind::CrossOracle => "cross-oracle",
            EdgeKind::Back => "back",
        }
    }
}

#[derive(Debug)]
pub struct EdgeData {
    pub from: String,
    pub to: String,
    pub kind: EdgeKind,
    /// Set for `CrossOracle`/`Back` edges: the oracle name the edge jumps to
    /// (or back into), shown as a small label on the edge.
    pub label: Option<String>,
}

impl EdgeData {
    pub fn dependency(from: String, to: String) -> Self {
        EdgeData {
            from,
            to,
            kind: EdgeKind::Dependency,
            label: None,
        }
    }
}

pub struct ClusterData {
    pub oracle_name: String,
    /// Display heading for the cluster -- equal to `oracle_name` for a
    /// normal per-oracle cluster, but distinct for an invariant-flow
    /// cross-oracle cluster (`"{other_oracle} · {fragment_name}"`), whose
    /// nodes still carry the real `oracle_name` so panel/search features
    /// that key off it keep working.
    pub label: String,
    pub x: f64,
    pub y: f64,
    pub width: f64,
    pub height: f64,
    pub nodes: Vec<NodeData>,
    pub edges: Vec<EdgeData>,
}

/// One oracle's "invariant flow" graph (see
/// [`crate::writers::html::build_invariant_flow_graph`]): starting from its
/// `same-output`/`equal-aborts` obligations, follows normal dependency edges
/// plus `with invariants` edges out to the invariant fragments they need,
/// each of which additionally gets its own freshly expanded cluster per
/// other oracle that also establishes it (a `CrossOracle`/`Back` edge in
/// `cross_edges`, not `clusters[i].edges`, since those connect nodes across
/// different clusters).
pub struct FlowGraphData {
    pub oracle_name: String,
    pub width: f64,
    pub height: f64,
    pub clusters: Vec<ClusterData>,
    pub cross_edges: Vec<EdgeData>,
}

pub struct GraphData {
    pub graph_name: String,
    pub label: String,
    pub width: f64,
    pub height: f64,
    pub clusters: Vec<ClusterData>,
    pub invariant_flows: Vec<FlowGraphData>,
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                write!(out, "\\u{:04x}", c as u32).unwrap();
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_opt_string(s: &Option<String>) -> String {
    match s {
        Some(s) => json_string(s),
        None => "null".to_string(),
    }
}

fn json_opt_bool(b: Option<bool>) -> &'static str {
    match b {
        Some(true) => "true",
        Some(false) => "false",
        None => "null",
    }
}

impl ReferencedDefinition {
    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"name\":{},\"kindLabel\":{},\"dominoSource\":{},\"easycryptSource\":{}}}",
            json_string(&self.name),
            json_string(self.kind_label),
            json_string(&self.domino_source),
            json_string(&self.easycrypt_source),
        )
        .unwrap();
    }
}

impl NodeData {
    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"id\":{},\"name\":{},\"x\":{},\"y\":{},\"width\":{},\"height\":{},\
             \"fillColor\":{},\"claimType\":{},\"builtin\":{},\"admitted\":{},\
             \"dependsOnNewState\":{},\"implicit\":{},\"dominoSource\":{},\"easycryptSource\":{},\
             \"referencedDefinitions\":",
            json_string(&self.id),
            json_string(&self.name),
            self.x,
            self.y,
            self.width,
            self.height,
            json_string(self.fill_color),
            json_string(self.claim_type),
            self.builtin,
            self.admitted,
            json_opt_bool(self.depends_on_new_state),
            self.implicit,
            json_opt_string(&self.domino_source),
            json_opt_string(&self.easycrypt_source),
        )
        .unwrap();
        write_json_array(
            out,
            &self.referenced_definitions,
            ReferencedDefinition::write_json,
        );
        out.push('}');
    }
}

impl EdgeData {
    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"from\":{},\"to\":{},\"kind\":{},\"label\":{}}}",
            json_string(&self.from),
            json_string(&self.to),
            json_string(self.kind.as_str()),
            json_opt_string(&self.label),
        )
        .unwrap();
    }
}

fn write_json_array<T>(out: &mut String, items: &[T], write_one: impl Fn(&T, &mut String)) {
    out.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_one(item, out);
    }
    out.push(']');
}

impl ClusterData {
    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"oracleName\":{},\"label\":{},\"x\":{},\"y\":{},\"width\":{},\"height\":{},\"nodes\":",
            json_string(&self.oracle_name),
            json_string(&self.label),
            self.x,
            self.y,
            self.width,
            self.height,
        )
        .unwrap();
        write_json_array(out, &self.nodes, NodeData::write_json);
        out.push_str(",\"edges\":");
        write_json_array(out, &self.edges, EdgeData::write_json);
        out.push('}');
    }
}

impl FlowGraphData {
    fn write_json(&self, out: &mut String) {
        write!(
            out,
            "{{\"oracleName\":{},\"width\":{},\"height\":{},\"clusters\":",
            json_string(&self.oracle_name),
            self.width,
            self.height,
        )
        .unwrap();
        write_json_array(out, &self.clusters, ClusterData::write_json);
        out.push_str(",\"crossEdges\":");
        write_json_array(out, &self.cross_edges, EdgeData::write_json);
        out.push('}');
    }
}

impl GraphData {
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        write!(
            out,
            "{{\"graphName\":{},\"label\":{},\"width\":{},\"height\":{},\"clusters\":",
            json_string(&self.graph_name),
            json_string(&self.label),
            self.width,
            self.height,
        )
        .unwrap();
        write_json_array(&mut out, &self.clusters, ClusterData::write_json);
        out.push_str(",\"invariantFlows\":");
        write_json_array(&mut out, &self.invariant_flows, FlowGraphData::write_json);
        out.push('}');
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_quotes_backslashes_and_newlines() {
        let s = json_string("a\"b\\c\nd");
        assert_eq!(s, "\"a\\\"b\\\\c\\nd\"");
    }

    #[test]
    fn empty_graph_serializes_to_empty_cluster_array() {
        let g = GraphData {
            graph_name: "g".to_string(),
            label: "l".to_string(),
            width: 0.0,
            height: 0.0,
            clusters: vec![],
            invariant_flows: vec![],
        };
        assert_eq!(
            g.to_json(),
            "{\"graphName\":\"g\",\"label\":\"l\",\"width\":0,\"height\":0,\"clusters\":[],\"invariantFlows\":[]}"
        );
    }

    #[test]
    fn node_with_no_source_and_unknown_classification_uses_json_null() {
        let n = NodeData {
            id: "o::c".to_string(),
            name: "c".to_string(),
            x: 1.0,
            y: 2.0,
            width: 10.0,
            height: 5.0,
            fill_color: "lightgray",
            claim_type: "Lemma",
            builtin: false,
            admitted: false,
            depends_on_new_state: None,
            implicit: true,
            domino_source: None,
            easycrypt_source: None,
            referenced_definitions: vec![],
        };
        let mut out = String::new();
        n.write_json(&mut out);
        assert!(out.contains("\"dependsOnNewState\":null"));
        assert!(out.contains("\"dominoSource\":null"));
        assert!(out.contains("\"referencedDefinitions\":[]"));
        assert!(out.contains("\"easycryptSource\":null"));
    }
}
