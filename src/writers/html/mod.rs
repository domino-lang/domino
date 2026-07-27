// SPDX-License-Identifier: MIT OR Apache-2.0

//! Renders the lemma dependency trees of an `equivalence`/`hybrid` game hop
//! as a single self-contained, static HTML page: an infinite pan/zoom canvas
//! with the same claim-tree structure and annotations as
//! [`crate::writers::dot`], plus click-to-inspect Domino source and (later)
//! an EasyCrypt-flavored translation of each claim's SMT body.
//!
//! The page has no external dependencies (no CDN scripts, no fonts) so it
//! can be dropped straight onto GitHub Pages.

pub mod data;
pub mod layout;

use std::collections::{BTreeMap, BTreeSet};

use data::{ClusterData, EdgeData, GraphData, NodeData, ReferencedDefinition};
use layout::LayoutParams;

use crate::theorem::Claim;
use crate::writers::claim_source;
use crate::writers::claim_source::ClaimSource;
use crate::writers::dot::{claim_fillcolor, is_builtin_claim_name};

const CLUSTER_GAP: f64 = 80.0;
const LABEL_HEIGHT: f64 = 40.0;

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// SMT-LIB atom characters (per `src/util/smtparser/smt.pest`'s `atom` rule)
/// -- used to check that a name match in raw source text is a whole
/// identifier, not a substring of a longer one (e.g. `no-abort` shouldn't
/// match inside `left-no-abort`).
fn is_smt_atom_char(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '_' | '-' | '=' | '<' | '>' | '$' | '!' | '+' | '@' | '.' | '*'
        )
}

/// Whether `needle` appears in `haystack` as a whole identifier (not as part
/// of a longer one).
fn contains_whole_identifier(haystack: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return false;
    }
    let mut search_from = 0;
    while let Some(offset) = haystack[search_from..].find(needle) {
        let start = search_from + offset;
        let end = start + needle.len();
        let before_is_boundary = haystack[..start]
            .chars()
            .next_back()
            .is_none_or(|c| !is_smt_atom_char(c));
        let after_is_boundary = haystack[end..]
            .chars()
            .next()
            .is_none_or(|c| !is_smt_atom_char(c));
        if before_is_boundary && after_is_boundary {
            return true;
        }
        search_from = start + 1;
    }
    false
}

fn referenced_definition_kind_label(kind: claim_source::ClaimKind) -> &'static str {
    match kind {
        claim_source::ClaimKind::Lemma => "Lemma",
        claim_source::ClaimKind::StateRelation => "State relation",
        claim_source::ClaimKind::Function => "Helper function",
    }
}

/// Finds every other captured definition in `sources` that `claim_source`'s
/// raw Domino text calls -- a plain `define-fun` helper, or another
/// lemma/relation -- so the panel can show their definitions inline instead
/// of making a reviewer go hunting for them. Best-effort text search (see
/// [`contains_whole_identifier`]), not a real call-graph analysis: it can't
/// see through further indirection, but every real example this was tested
/// against calls its helpers directly.
fn find_referenced_definitions(
    self_key: &str,
    claim_source: &ClaimSource,
    sources: &BTreeMap<String, ClaimSource>,
) -> Vec<ReferencedDefinition> {
    sources
        .iter()
        .filter(|(name, _)| name.as_str() != self_key)
        .filter(|(name, _)| contains_whole_identifier(&claim_source.domino_source, name))
        .map(|(name, src)| ReferencedDefinition {
            name: name.clone(),
            kind_label: referenced_definition_kind_label(src.kind),
            domino_source: src.domino_source.clone(),
            easycrypt_source: src.easycrypt_source.clone(),
        })
        .collect()
}

/// The SMT function name Domino's own proof pipeline looks a claim up under
/// -- see `Relation::function_name` (`src/writers/smt/patterns/functions/relation.rs`)
/// and its callers in `src/writers/smt/contexts/equivalence/emit.rs`.
/// `ClaimType::Lemma` claims (the common case: any claim name that doesn't
/// happen to start with `relation`/`invariant`) get mangled into
/// `<relation-{name}-{left}-{right}-{oracle}>`; `ClaimType::Relation` and
/// `ClaimType::Invariant` claims are asserted under their bare name
/// unchanged. Getting this wrong doesn't corrupt anything (a claim source
/// lookup just misses and falls back to "source not captured"), but it *did*
/// silently miss almost every real user-authored lemma before this existed,
/// since bare-name lookup only ever matched the (rarer) relation/invariant
/// case.
fn claim_smt_lookup_key(
    claim: &Claim,
    left_name: &str,
    right_name: &str,
    oracle_name: &str,
) -> String {
    match claim.ty() {
        crate::theorem::ClaimType::Lemma => {
            format!(
                "<relation-{}-{left_name}-{right_name}-{oracle_name}>",
                claim.name()
            )
        }
        _ => claim.name().to_string(),
    }
}

/// Builds one oracle's cluster: same node set (declared claims + implicit
/// undeclared/builtin dependency stubs) and edges as
/// [`crate::writers::dot::write_claim_tree_body`], laid out with
/// [`layout::layered_layout`].
#[allow(clippy::too_many_arguments)]
fn build_cluster(
    left_name: &str,
    right_name: &str,
    oracle_name: &str,
    tree: &[Claim],
    sources: Option<&BTreeMap<String, ClaimSource>>,
    params: &LayoutParams,
) -> ClusterData {
    let node_id = |name: &str| format!("{oracle_name}::{name}");
    let known: BTreeSet<&str> = tree.iter().map(Claim::name).collect();

    let mut implicit: Vec<&str> = tree
        .iter()
        .flat_map(Claim::dependencies)
        .map(String::as_str)
        .filter(|dep| !known.contains(dep))
        .collect();
    implicit.sort_unstable();
    implicit.dedup();

    let mut node_ids: Vec<String> = tree.iter().map(|c| node_id(c.name())).collect();
    node_ids.extend(implicit.iter().map(|dep| node_id(dep)));

    let edges: Vec<(String, String)> = tree
        .iter()
        .flat_map(|claim| {
            claim
                .dependencies()
                .iter()
                .map(move |dep| (node_id(claim.name()), node_id(dep)))
        })
        .collect();

    let layout = layout::layered_layout(&node_ids, &edges, params);
    let positions: BTreeMap<&str, (f64, f64)> = layout
        .nodes
        .iter()
        .map(|n| (n.id.as_str(), (n.x, n.y + LABEL_HEIGHT)))
        .collect();

    let mut nodes = Vec::with_capacity(node_ids.len());
    for claim in tree {
        let id = node_id(claim.name());
        let (x, y) = positions.get(id.as_str()).copied().unwrap_or((0.0, 0.0));
        let builtin = is_builtin_claim_name(claim.name());
        let lookup_key = claim_smt_lookup_key(claim, left_name, right_name, oracle_name);
        let source = sources.and_then(|s| s.get(&lookup_key));
        // Prefer ground truth from the invariant source (which macro form
        // actually defined this claim) over `claim.ty()`'s name-prefix
        // guess, which the common `relation-lemma-...` naming convention
        // fools into reading lemmas as state relations.
        let effective_ty = match source.map(|s| s.kind) {
            Some(claim_source::ClaimKind::StateRelation) => crate::theorem::ClaimType::Relation,
            Some(claim_source::ClaimKind::Lemma) => crate::theorem::ClaimType::Lemma,
            // A claim name colliding with a captured `define-fun` helper's
            // name would be a strange coincidence, not a real signal -- fall
            // back to the plain name-prefix guess same as no match at all.
            Some(claim_source::ClaimKind::Function) | None => claim.ty(),
        };
        nodes.push(NodeData {
            id,
            name: claim.name().to_string(),
            x,
            y,
            width: params.node_width,
            height: params.node_height,
            fill_color: if builtin {
                "lightgray"
            } else {
                claim_fillcolor(effective_ty)
            },
            claim_type: claim_type_label(effective_ty),
            builtin,
            admitted: claim.is_admitted(),
            depends_on_new_state: source.map(|s| s.depends_on_new_state),
            implicit: false,
            domino_source: source.map(|s| s.domino_source.clone()),
            easycrypt_source: source.map(|s| s.easycrypt_source.clone()),
            referenced_definitions: match (source, sources) {
                (Some(src), Some(all)) => find_referenced_definitions(&lookup_key, src, all),
                _ => Vec::new(),
            },
        });
    }
    for dep in &implicit {
        let id = node_id(dep);
        let (x, y) = positions.get(id.as_str()).copied().unwrap_or((0.0, 0.0));
        let builtin = is_builtin_claim_name(dep);
        nodes.push(NodeData {
            id,
            name: dep.to_string(),
            x,
            y,
            width: params.node_width,
            height: params.node_height,
            fill_color: "lightgray",
            claim_type: if builtin { "Builtin" } else { "Undeclared" },
            builtin,
            admitted: false,
            depends_on_new_state: None,
            implicit: true,
            domino_source: None,
            easycrypt_source: None,
            referenced_definitions: Vec::new(),
        });
    }

    let edges = edges
        .into_iter()
        .map(|(from, to)| EdgeData { from, to })
        .collect();

    ClusterData {
        oracle_name: oracle_name.to_string(),
        x: 0.0,
        y: 0.0,
        width: layout.width.max(params.node_width),
        height: layout.height + LABEL_HEIGHT,
        nodes,
        edges,
    }
}

fn claim_type_label(ty: crate::theorem::ClaimType) -> &'static str {
    use crate::theorem::ClaimType;
    match ty {
        ClaimType::Lemma => "Lemma",
        ClaimType::Relation => "Relation",
        ClaimType::Invariant => "Invariant",
        ClaimType::LeftPackageInvariant => "LeftPackageInvariant",
        ClaimType::RightPackageInvariant => "RightPackageInvariant",
        ClaimType::LeftGameInvariant => "LeftGameInvariant",
        ClaimType::RightGameInvariant => "RightGameInvariant",
        ClaimType::InitialState => "InitialState",
    }
}

/// Renders the lemma dependency trees of every oracle of an
/// `equivalence`/`hybrid` game hop into a single self-contained HTML page,
/// one side-by-side cluster per oracle -- the HTML analogue of
/// [`crate::writers::dot::lemma_dependency_dot`].
///
/// `left_name`/`right_name` are the two game instance names of the
/// equivalence/hybrid hop (as passed to e.g. `Project::write_lemma_dependency_dot`)
/// -- needed, alongside each oracle's name, to reconstruct the mangled SMT
/// function name Domino's own proof pipeline looks `ClaimType::Lemma` claims
/// up under (see [`claim_smt_lookup_key`]).
///
/// `claim_sources` provides, per oracle, the verbatim Domino source and
/// old-state-only/depends-on-new-state classification for each
/// `define-lemma`/`define-state-relation` claim (see
/// [`crate::writers::claim_source`]); pass an empty map for an oracle to
/// fall back to "source not captured" for all of its nodes.
pub fn lemma_dependency_html(
    graph_name: &str,
    label: &str,
    left_name: &str,
    right_name: &str,
    trees: &[(String, Vec<Claim>)],
    claim_sources: &[(String, BTreeMap<String, ClaimSource>)],
) -> String {
    let params = LayoutParams::default();

    let mut clusters: Vec<ClusterData> = trees
        .iter()
        .map(|(oracle_name, tree)| {
            let sources = claim_sources
                .iter()
                .find(|(name, _)| name == oracle_name)
                .map(|(_, m)| m);
            build_cluster(left_name, right_name, oracle_name, tree, sources, &params)
        })
        .collect();

    let mut x_cursor = 0.0;
    let mut max_height: f64 = 0.0;
    for cluster in &mut clusters {
        cluster.x = x_cursor;
        cluster.y = 0.0;
        x_cursor += cluster.width + CLUSTER_GAP;
        max_height = max_height.max(cluster.height);
    }
    let total_width = (x_cursor - CLUSTER_GAP).max(0.0);

    let graph_data = GraphData {
        graph_name: graph_name.to_string(),
        label: label.to_string(),
        width: total_width,
        height: max_height,
        clusters,
    };

    let json = graph_data.to_json().replace("</", "<\\/");

    TEMPLATE
        .replace("__TITLE__", &html_escape(label))
        .replace("__GRAPH_DATA_JSON__", &json)
}

const TEMPLATE: &str = include_str!("template.html");
