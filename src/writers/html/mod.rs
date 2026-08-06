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

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use data::{
    ClusterData, EdgeData, EdgeKind, FlowGraphData, GraphData, NodeData, ReferencedDefinition,
};
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

/// Finds every other captured *non-function* definition in `sources` that
/// `claim_source`'s raw Domino text calls -- transitively: another
/// lemma/relation, and anything referenced from within those in turn (a
/// relation calling another relation, or reached indirectly through a helper
/// function's own body), so the panel can show every definition a reviewer
/// would need without having to click through each one by hand.
///
/// Plain `define-fun` helpers are deliberately excluded from the *result*
/// (though their bodies are still walked into, same as any other match) --
/// they're promoted to first-class graph nodes with their own direct edges
/// by [`build_cluster`]'s helper-function BFS instead, so listing them here
/// too would just be duplication.
///
/// This is a breadth-first search over the "mentions this other name"
/// relation (see [`contains_whole_identifier`]) starting from `claim_source`
/// itself, so the result is ordered shallowest-first: names the claim calls
/// directly come before names only reached through one of those. It's still
/// best-effort text search rather than true call-graph analysis (it can miss
/// a reference built up dynamically rather than written as a literal name),
/// but unlike a single-level scan it no longer stops at the first hop, and
/// visiting each name at most once makes it safe against reference cycles.
fn find_referenced_definitions(
    self_key: &str,
    claim_source: &ClaimSource,
    sources: &BTreeMap<String, ClaimSource>,
) -> Vec<ReferencedDefinition> {
    let mut visited: BTreeSet<&str> = BTreeSet::new();
    visited.insert(self_key);

    let mut queue: VecDeque<&str> = VecDeque::new();
    queue.push_back(claim_source.domino_source.as_str());

    let mut result = Vec::new();
    while let Some(text) = queue.pop_front() {
        for (name, src) in sources.iter() {
            if visited.contains(name.as_str()) || !contains_whole_identifier(text, name) {
                continue;
            }
            visited.insert(name.as_str());
            if src.kind != claim_source::ClaimKind::Function {
                result.push(ReferencedDefinition {
                    name: name.clone(),
                    kind_label: referenced_definition_kind_label(src.kind),
                    domino_source: src.domino_source.clone(),
                    easycrypt_source: src.easycrypt_source.clone(),
                });
            }
            queue.push_back(src.domino_source.as_str());
        }
    }
    result
}

/// BFS over the "calls this helper function" relation (see
/// [`contains_whole_identifier`]), starting from every `root`'s own text and
/// following helper-calling-helper chains -- the same one-hop-at-a-time
/// shape as the claim-dependency edges in [`build_cluster`], but restricted
/// to `ClaimKind::Function` targets so it can feed the layout algorithm a
/// proper node+edge graph (unlike [`find_referenced_definitions`]'s flat,
/// transitively-collapsed list). Returns the discovered function names
/// (each returned once, sorted, regardless of how many roots or helpers call
/// it) and every direct call edge as `(caller_id, "{oracle_name}::{callee}")`
/// pairs -- note a shared helper naturally ends up with more than one
/// incoming edge here, from each distinct caller.
fn find_function_calls<'a>(
    roots: impl IntoIterator<Item = (String, &'a str)>,
    oracle_name: &str,
    sources: &'a BTreeMap<String, ClaimSource>,
) -> (Vec<&'a str>, Vec<(String, String)>) {
    let node_id = |name: &str| format!("{oracle_name}::{name}");
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut queue: VecDeque<(String, &str)> = VecDeque::new();
    queue.extend(roots);

    let mut names = Vec::new();
    let mut edges = Vec::new();
    while let Some((from_id, text)) = queue.pop_front() {
        for (name, src) in sources.iter() {
            let to_id = node_id(name);
            if src.kind != claim_source::ClaimKind::Function
                || to_id == from_id
                || !contains_whole_identifier(text, name)
            {
                continue;
            }
            edges.push((from_id.clone(), to_id));
            if seen.insert(name.as_str()) {
                names.push(name.as_str());
                queue.push_back((node_id(name), src.domino_source.as_str()));
            }
        }
    }
    names.sort_unstable();
    (names, edges)
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

/// Names of every `define-state-relation` invariant fragment captured for
/// one oracle, from its `sources` map -- ground truth (see
/// [`claim_source::ClaimKind::StateRelation`]), independent of whether the
/// theorem's `lemmas {}` block happens to mention any of them by name.
fn fragment_names(sources: Option<&BTreeMap<String, ClaimSource>>) -> BTreeSet<&str> {
    sources
        .into_iter()
        .flatten()
        .filter(|(_, src)| src.kind == claim_source::ClaimKind::StateRelation)
        .map(|(name, _)| name.as_str())
        .collect()
}

/// Mirrors `EquivalenceSmtDriver::reconcile_invariant_fragment_claims`
/// (`src/gamehops/equivalence/verify_fn.rs`) for the HTML/dot exporters,
/// which build their claim trees straight from the parsed theorem rather
/// than from a loaded `EquivalenceContext` (see this module's doc comment):
/// every fragment not already covered by an explicit `lemmas {}` entry gets
/// a synthesized claim depending only on `no-abort` (exactly what domino
/// auto-generates and proves at `prove` time), and any existing claim
/// sharing a fragment's name gets corrected from `ClaimType::guess_from_name`'s
/// `Lemma` guess to `Invariant` -- a fragment is never actually
/// `define-lemma`-shaped, so the name-prefix guess is simply wrong for it.
/// Without this, an un-declared fragment (the common case -- fragments are
/// auto-proved whether or not the theorem mentions them) would never appear
/// in the graph at all, since [`crate::gamehops::equivalence::EquivalenceSmtDriver::validate_claim_dependencies`]
/// forbids ever listing one as a plain `dependencies()` entry, so it can't
/// even surface as an implicit/undeclared stub the way a missing lemma can.
fn reconcile_invariant_fragments(tree: &[Claim], fragments: &BTreeSet<&str>) -> Vec<Claim> {
    let mut claims: Vec<Claim> = tree.to_vec();
    for claim in claims.iter_mut() {
        if claim.ty() == crate::theorem::ClaimType::Lemma && fragments.contains(claim.name()) {
            claim.ty = crate::theorem::ClaimType::Invariant;
        }
    }
    let known: BTreeSet<&str> = claims.iter().map(Claim::name).collect();
    let mut missing: Vec<&str> = fragments
        .iter()
        .filter(|name| !known.contains(*name))
        .copied()
        .collect();
    missing.sort_unstable();
    for name in missing {
        claims.push(Claim {
            name: name.to_string(),
            ty: crate::theorem::ClaimType::Invariant,
            dependencies: vec!["no-abort".to_string()],
            admitted: false,
            user_declared: false,
            invariant_scope: None,
        });
    }
    claims
}

/// Builds one oracle's cluster: same node set (declared claims + implicit
/// undeclared/builtin dependency stubs) and edges as
/// [`crate::writers::dot::write_claim_tree_body`], plus (HTML-only) helper
/// (`define-fun`) function nodes discovered from the claims' own Domino
/// source via [`find_function_calls`], laid out with
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

    let fragments = fragment_names(sources);
    let tree: Vec<Claim> = reconcile_invariant_fragments(tree, &fragments);
    let tree = tree.as_slice();

    let known: BTreeSet<&str> = tree.iter().map(Claim::name).collect();

    let mut implicit: Vec<&str> = tree
        .iter()
        .flat_map(Claim::dependencies)
        .map(String::as_str)
        .filter(|dep| !known.contains(dep))
        .collect();
    implicit.sort_unstable();
    implicit.dedup();

    // Helper ("define-fun") functions any declared claim calls, directly or
    // through a chain of other helpers -- promoted to their own nodes with
    // their own direct edges (see `find_function_calls`) rather than only
    // showing up nested in the calling claim's detail panel, so a helper
    // shared by several oracles' claims is visible as the same-named node in
    // each of their clusters (`sources` is captured per oracle, so it can't
    // be a single shared node) and the cross-oracle reuse becomes visible
    // both through the graph and the "also referenced in oracle(s)" panel
    // section (see `template.html`).
    let (function_nodes, function_edges) = match sources {
        Some(sources) => {
            let roots = tree.iter().filter_map(|claim| {
                let lookup_key = claim_smt_lookup_key(claim, left_name, right_name, oracle_name);
                sources
                    .get(&lookup_key)
                    .map(|src| (node_id(claim.name()), src.domino_source.as_str()))
            });
            find_function_calls(roots, oracle_name, sources)
        }
        None => (Vec::new(), Vec::new()),
    };

    let mut node_ids: Vec<String> = tree.iter().map(|c| node_id(c.name())).collect();
    node_ids.extend(implicit.iter().map(|dep| node_id(dep)));
    node_ids.extend(function_nodes.iter().map(|name| node_id(name)));

    let mut edges: Vec<(String, String, EdgeKind)> = tree
        .iter()
        .flat_map(|claim| {
            claim
                .dependencies()
                .iter()
                .map(move |dep| (node_id(claim.name()), node_id(dep), EdgeKind::Dependency))
        })
        .collect();
    edges.extend(
        function_edges
            .into_iter()
            .map(|(from, to)| (from, to, EdgeKind::Dependency)),
    );

    // An explicit `with invariants [...]` modifier: draw an edge to each
    // named fragment (best-effort -- `validate_invariant_scopes` already
    // rejects an unknown fragment name at `prove` time, so silently skipping
    // one here just means this exporter degrades gracefully instead of
    // panicking on an otherwise-invalid theorem it's still asked to render).
    for claim in tree {
        let Some(scope) = &claim.invariant_scope else {
            continue;
        };
        for fragment_name in scope {
            if !fragments.contains(fragment_name.as_str()) {
                continue;
            }
            edges.push((
                node_id(claim.name()),
                node_id(fragment_name),
                EdgeKind::WithInvariants,
            ));
        }
    }

    let layout_edges: Vec<(String, String)> = edges
        .iter()
        .map(|(from, to, _)| (from.clone(), to.clone()))
        .collect();
    let layout = layout::layered_layout(&node_ids, &layout_edges, params);
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
        // fools into reading lemmas as state relations. A `StateRelation`
        // source doesn't need the same override: `reconcile_invariant_fragments`
        // above already resolved its `ClaimType` to `Relation`/`Invariant`
        // (mirroring `EquivalenceSmtDriver::reconcile_invariant_fragment_claims`'s
        // naming-convention split) more precisely than a blanket "always
        // `Relation`" guess would.
        let effective_ty = match source.map(|s| s.kind) {
            Some(claim_source::ClaimKind::Lemma) => crate::theorem::ClaimType::Lemma,
            // A claim name colliding with a captured `define-fun` helper's
            // name would be a strange coincidence, not a real signal -- fall
            // back to the already-reconciled `ClaimType` same as no match at
            // all.
            Some(claim_source::ClaimKind::StateRelation)
            | Some(claim_source::ClaimKind::Function)
            | None => claim.ty(),
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
    if let Some(sources) = sources {
        for name in &function_nodes {
            let id = node_id(name);
            let (x, y) = positions.get(id.as_str()).copied().unwrap_or((0.0, 0.0));
            // Present by construction: `name` only ever came from iterating
            // this same `sources` map in `find_function_calls`.
            let src = sources.get(*name).expect("function source must exist");
            nodes.push(NodeData {
                id,
                name: name.to_string(),
                x,
                y,
                width: params.node_width,
                height: params.node_height,
                fill_color: "wheat",
                claim_type: "Helper function",
                builtin: false,
                admitted: false,
                // Doesn't apply: a `define-fun` helper isn't asserted about
                // a specific oracle call the way a lemma/relation is, so
                // there's no old-state-vs-new-state distinction to draw.
                depends_on_new_state: None,
                implicit: false,
                domino_source: Some(src.domino_source.clone()),
                easycrypt_source: Some(src.easycrypt_source.clone()),
                referenced_definitions: find_referenced_definitions(name, src, sources),
            });
        }
    }

    let edges = edges
        .into_iter()
        .map(|(from, to, kind)| EdgeData {
            from,
            to,
            kind,
            label: None,
        })
        .collect();

    ClusterData {
        oracle_name: oracle_name.to_string(),
        label: oracle_name.to_string(),
        x: 0.0,
        y: 0.0,
        width: layout.width.max(params.node_width),
        height: layout.height + LABEL_HEIGHT,
        nodes,
        edges,
    }
}

/// Lays clusters out left-to-right (same shape [`lemma_dependency_html`] uses
/// for its top-level per-oracle clusters), mutating each cluster's `x`/`y` in
/// place and returning the overall `(width, height)` this arrangement needs.
fn arrange_clusters_left_to_right(clusters: &mut [ClusterData]) -> (f64, f64) {
    let mut x_cursor = 0.0;
    let mut max_height: f64 = 0.0;
    for cluster in clusters.iter_mut() {
        cluster.x = x_cursor;
        cluster.y = 0.0;
        x_cursor += cluster.width + CLUSTER_GAP;
        max_height = max_height.max(cluster.height);
    }
    let total_width = (x_cursor - CLUSTER_GAP).max(0.0);
    (total_width, max_height)
}

/// A lookup over every oracle's already-built cluster (see [`build_cluster`]),
/// used by [`build_invariant_flow_graph`] to jump between oracles: every
/// node and its local outgoing edges, keyed by the same `{oracle}::{name}`
/// id `build_cluster` assigns, plus a name -> declaring-oracles index for
/// non-implicit, non-builtin `Relation`/`Invariant` nodes (i.e. claims
/// backed by a `define-state-relation` -- both the fragment-promoted
/// `Invariant` case and the pre-existing hand-chained `relation-*` naming
/// convention, see [`reconcile_invariant_fragments`]) -- the set of claims a
/// `with invariants [...]` edge can actually point at.
struct FlowIndex<'a> {
    node_by_id: BTreeMap<String, &'a NodeData>,
    outgoing: BTreeMap<String, Vec<(String, EdgeKind)>>,
    fragment_oracles: BTreeMap<String, Vec<String>>,
}

impl<'a> FlowIndex<'a> {
    fn build(clusters: &'a [ClusterData]) -> Self {
        let mut node_by_id = BTreeMap::new();
        let mut outgoing: BTreeMap<String, Vec<(String, EdgeKind)>> = BTreeMap::new();
        let mut fragment_oracles: BTreeMap<String, Vec<String>> = BTreeMap::new();

        for cluster in clusters {
            for node in &cluster.nodes {
                node_by_id.insert(node.id.clone(), node);
                if !node.builtin
                    && !node.implicit
                    && matches!(node.claim_type, "Relation" | "Invariant")
                {
                    fragment_oracles
                        .entry(node.name.clone())
                        .or_default()
                        .push(cluster.oracle_name.clone());
                }
            }
            for edge in &cluster.edges {
                outgoing
                    .entry(edge.from.clone())
                    .or_default()
                    .push((edge.to.clone(), edge.kind));
            }
        }
        for oracles in fragment_oracles.values_mut() {
            oracles.sort_unstable();
            oracles.dedup();
        }

        FlowIndex {
            node_by_id,
            outgoing,
            fragment_oracles,
        }
    }
}

/// Wraps a freshly walked cluster's nodes/edges into a [`ClusterData`],
/// running them through [`layout::layered_layout`] the same way
/// [`build_cluster`] does (each invariant-flow cluster is laid out
/// independently of every other one, root or virtual).
fn finish_flow_cluster(
    label: String,
    oracle_name: &str,
    mut nodes: Vec<NodeData>,
    edges: Vec<EdgeData>,
    params: &LayoutParams,
) -> ClusterData {
    let node_ids: Vec<String> = nodes.iter().map(|n| n.id.clone()).collect();
    let layout_edges: Vec<(String, String)> = edges
        .iter()
        .map(|e| (e.from.clone(), e.to.clone()))
        .collect();
    let layout = layout::layered_layout(&node_ids, &layout_edges, params);
    let positions: BTreeMap<&str, (f64, f64)> = layout
        .nodes
        .iter()
        .map(|n| (n.id.as_str(), (n.x, n.y + LABEL_HEIGHT)))
        .collect();
    for node in nodes.iter_mut() {
        let (x, y) = positions
            .get(node.id.as_str())
            .copied()
            .unwrap_or((0.0, 0.0));
        node.x = x;
        node.y = y;
    }

    ClusterData {
        oracle_name: oracle_name.to_string(),
        label,
        x: 0.0,
        y: 0.0,
        width: layout.width.max(params.node_width),
        height: layout.height + LABEL_HEIGHT,
        nodes,
        edges,
    }
}

/// Walks the "invariant flow" of one oracle -- see [`build_invariant_flow_graph`]'s
/// doc comment for the algorithm. Threaded through the whole recursive walk
/// (both the local, same-cluster dependency walk and the cross-oracle jumps
/// it triggers), so it's a struct rather than a bare function plus
/// parameters.
struct FlowBuilder<'a, 'b> {
    index: &'b FlowIndex<'a>,
    params: &'b LayoutParams,
    id_counter: usize,
    /// Clusters spawned by a cross-oracle jump, in the order they were
    /// created -- the root cluster (built by the caller) is prepended to
    /// these to form the final cluster list.
    extra_clusters: Vec<ClusterData>,
    cross_edges: Vec<EdgeData>,
    /// `{oracle}::{fragment}` keys currently being expanded higher up the
    /// current path -- i.e. an actual ancestor, not merely "already drawn
    /// somewhere in the graph". Checked before following a cross-oracle
    /// candidate so a genuine cycle (a fragment depending, transitively, on
    /// itself holding in an old state) terminates with a `Back` edge, while
    /// the very same fragment/oracle pair reached again via a *different,
    /// unrelated* branch still gets its own fresh expansion.
    ancestors: Vec<String>,
    ancestor_flow_id: BTreeMap<String, String>,
}

impl<'a, 'b> FlowBuilder<'a, 'b> {
    fn fresh_id(&mut self) -> String {
        self.id_counter += 1;
        format!("flow-{}", self.id_counter)
    }

    /// Places `real_id` in the current cluster (memoized via `local_memo`,
    /// scoped to that one cluster, so a diamond within one oracle's own
    /// dependency chain collapses to a single node instead of duplicating
    /// it) and recurses into its outgoing edges: a plain `Dependency` edge
    /// stays within the same cluster/oracle, while a `WithInvariants` edge's
    /// target additionally triggers [`Self::branch_cross_oracle`] the first
    /// time it's placed (not on a `local_memo` hit -- otherwise two claims
    /// in the same oracle both scoping to the same fragment would branch
    /// twice). Returns `real_id`'s flow-local id.
    fn expand_local(
        &mut self,
        real_id: &str,
        oracle_name: &str,
        nodes: &mut Vec<NodeData>,
        edges: &mut Vec<EdgeData>,
        local_memo: &mut BTreeMap<String, String>,
    ) -> String {
        if let Some(id) = local_memo.get(real_id) {
            return id.clone();
        }
        let flow_id = self.fresh_id();
        local_memo.insert(real_id.to_string(), flow_id.clone());

        let Some(&node_ref) = self.index.node_by_id.get(real_id) else {
            // Shouldn't happen (every edge target came from a real cluster's
            // own node list), but degrade gracefully rather than panic on a
            // stray id in an otherwise-invalid theorem this exporter is
            // still asked to render.
            return flow_id;
        };
        let mut node = node_ref.clone();
        node.id = flow_id.clone();
        nodes.push(node);

        let deps = self
            .index
            .outgoing
            .get(real_id)
            .cloned()
            .unwrap_or_default();
        for (dep_real_id, kind) in deps {
            let already_placed = local_memo.contains_key(&dep_real_id);
            let dep_flow_id =
                self.expand_local(&dep_real_id, oracle_name, nodes, edges, local_memo);
            edges.push(EdgeData {
                from: flow_id.clone(),
                to: dep_flow_id.clone(),
                kind,
                label: None,
            });
            if kind == EdgeKind::WithInvariants && !already_placed {
                if let Some(dep_name) = self.index.node_by_id.get(dep_real_id.as_str()) {
                    let dep_name = dep_name.name.clone();
                    self.branch_cross_oracle(oracle_name, &dep_name, &dep_flow_id);
                }
            }
        }
        flow_id
    }

    /// For `fragment_name` as established in `from_oracle` (the node already
    /// placed at `flow_id`), spawns one freshly expanded cluster per *other*
    /// oracle (including possibly `from_oracle` itself again, later on a
    /// different path -- see the module doc) that also declares this
    /// fragment, connected by a `CrossOracle` edge; a candidate that's
    /// already an ancestor of this exact call (a cycle) gets a `Back` edge
    /// to that ancestor's node instead of a new cluster.
    ///
    /// This call itself can be reentrant: two independent cross-oracle
    /// branches (each with their own fresh `local_memo`, so the local
    /// same-cluster memoization can't see each other) can both walk back
    /// into the same `(from_oracle, fragment_name)` pair. Without this
    /// check that reentrancy isn't a "different, unrelated branch" -- it's
    /// the same ancestor pair already being expanded further up the current
    /// call stack -- and would recurse forever instead of terminating with
    /// a `Back` edge.
    fn branch_cross_oracle(&mut self, from_oracle: &str, fragment_name: &str, flow_id: &str) {
        let key = format!("{from_oracle}::{fragment_name}");
        if let Some(ancestor_flow_id) = self.ancestor_flow_id.get(&key) {
            self.cross_edges.push(EdgeData {
                from: flow_id.to_string(),
                to: ancestor_flow_id.clone(),
                kind: EdgeKind::Back,
                label: Some(from_oracle.to_string()),
            });
            return;
        }
        self.ancestors.push(key.clone());
        self.ancestor_flow_id
            .insert(key.clone(), flow_id.to_string());

        let candidates = self
            .index
            .fragment_oracles
            .get(fragment_name)
            .cloned()
            .unwrap_or_default();
        for other_oracle in candidates {
            let other_key = format!("{other_oracle}::{fragment_name}");
            if self.ancestors.iter().any(|k| k == &other_key) {
                let back_id = self.ancestor_flow_id[&other_key].clone();
                self.cross_edges.push(EdgeData {
                    from: flow_id.to_string(),
                    to: back_id,
                    kind: EdgeKind::Back,
                    label: Some(other_oracle.clone()),
                });
                continue;
            }

            let other_real_id = format!("{other_oracle}::{fragment_name}");
            if !self.index.node_by_id.contains_key(&other_real_id) {
                continue;
            }
            let mut cluster_nodes = Vec::new();
            let mut cluster_edges = Vec::new();
            let mut local_memo = BTreeMap::new();
            let target_flow_id = self.expand_local(
                &other_real_id,
                &other_oracle,
                &mut cluster_nodes,
                &mut cluster_edges,
                &mut local_memo,
            );
            let cluster = finish_flow_cluster(
                format!("{other_oracle} \u{b7} {fragment_name}"),
                &other_oracle,
                cluster_nodes,
                cluster_edges,
                self.params,
            );
            self.extra_clusters.push(cluster);
            self.cross_edges.push(EdgeData {
                from: flow_id.to_string(),
                to: target_flow_id,
                kind: EdgeKind::CrossOracle,
                label: Some(other_oracle),
            });
        }

        self.ancestors.pop();
        self.ancestor_flow_id.remove(&key);
    }
}

/// Builds `root_oracle`'s "invariant flow" graph: starting from its
/// `same-output`/`equal-aborts` obligations, follows the exact same edges as
/// the main proof-tree graph (plain dependency hints, plus `with invariants`
/// scope edges -- see [`build_cluster`]) down through the lemmas and
/// invariant fragments they need. Every invariant fragment reached this way
/// additionally gets a `CrossOracle` edge into a freshly expanded, separately
/// laid out cluster for each *other* oracle (of the same equivalence hop)
/// that also declares it, showing how that oracle establishes it in turn --
/// recursively, since that oracle's own claims can themselves scope to
/// further fragments. A fragment/oracle pair already an ancestor of itself
/// on the current path (the temporal cycle inherent to an inductive
/// invariant -- e.g. "this fragment held in the old state" bottoming out at
/// "...which was itself established by some earlier call") is cut short with
/// a `Back` edge into the existing ancestor node rather than expanding
/// forever; the same pair reached again via an unrelated branch still gets
/// its own separate expansion.
///
/// `index` must be built from *every* oracle of the equivalence hop (not
/// just the ones actually being displayed), so a cross-oracle jump can find
/// its target even when the page is scoped to a single oracle via
/// `--oracle`. Returns `None` if `root_oracle` declares neither
/// `same-output` nor `equal-aborts` (nothing to root the graph at).
fn build_invariant_flow_graph(
    root_oracle: &str,
    index: &FlowIndex,
    params: &LayoutParams,
) -> Option<FlowGraphData> {
    let root_ids: Vec<String> = ["same-output", "equal-aborts"]
        .iter()
        .map(|name| format!("{root_oracle}::{name}"))
        .filter(|id| index.node_by_id.contains_key(id))
        .collect();
    if root_ids.is_empty() {
        return None;
    }

    let mut builder = FlowBuilder {
        index,
        params,
        id_counter: 0,
        extra_clusters: Vec::new(),
        cross_edges: Vec::new(),
        ancestors: Vec::new(),
        ancestor_flow_id: BTreeMap::new(),
    };

    let mut root_nodes = Vec::new();
    let mut root_edges = Vec::new();
    let mut local_memo = BTreeMap::new();
    for root_id in &root_ids {
        builder.expand_local(
            root_id,
            root_oracle,
            &mut root_nodes,
            &mut root_edges,
            &mut local_memo,
        );
    }
    let root_cluster = finish_flow_cluster(
        root_oracle.to_string(),
        root_oracle,
        root_nodes,
        root_edges,
        params,
    );

    let mut clusters = vec![root_cluster];
    clusters.extend(builder.extra_clusters);
    let (width, height) = arrange_clusters_left_to_right(&mut clusters);

    Some(FlowGraphData {
        oracle_name: root_oracle.to_string(),
        width,
        height,
        clusters,
        cross_edges: builder.cross_edges,
    })
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
///
/// `trees`/`claim_sources` scope what's actually *displayed* (mirroring
/// `--oracle`/`--claim`'s narrowing, same as before this parameter existed).
/// `all_trees`/`all_claim_sources` must always cover *every* oracle of the
/// equivalence hop, regardless of that scoping: the invariant-flow view's
/// cross-oracle jumps need to find their target oracle's claims even when
/// the displayed page has been narrowed down to just one. Pass the same
/// value for both pairs to display every oracle.
#[allow(clippy::too_many_arguments)]
pub fn lemma_dependency_html(
    graph_name: &str,
    label: &str,
    left_name: &str,
    right_name: &str,
    trees: &[(String, Vec<Claim>)],
    claim_sources: &[(String, BTreeMap<String, ClaimSource>)],
    all_trees: &[(String, Vec<Claim>)],
    all_claim_sources: &[(String, BTreeMap<String, ClaimSource>)],
) -> String {
    let params = LayoutParams::default();

    let build =
        |oracle_name: &str, tree: &[Claim], sources: &[(String, BTreeMap<String, ClaimSource>)]| {
            let sources = sources
                .iter()
                .find(|(name, _)| name == oracle_name)
                .map(|(_, m)| m);
            build_cluster(left_name, right_name, oracle_name, tree, sources, &params)
        };

    let mut clusters: Vec<ClusterData> = trees
        .iter()
        .map(|(oracle_name, tree)| build(oracle_name, tree, claim_sources))
        .collect();
    let (total_width, max_height) = arrange_clusters_left_to_right(&mut clusters);

    // Every oracle's cluster, unscoped by `--oracle`/`--claim`, purely as an
    // index for the invariant-flow view's cross-oracle jumps (see
    // `FlowIndex`) -- these are never themselves shown; only their
    // nodes/edges are read back out via `build_invariant_flow_graph`.
    let full_clusters: Vec<ClusterData> = all_trees
        .iter()
        .map(|(oracle_name, tree)| build(oracle_name, tree, all_claim_sources))
        .collect();
    let flow_index = FlowIndex::build(&full_clusters);
    let invariant_flows: Vec<FlowGraphData> = clusters
        .iter()
        .filter_map(|cluster| {
            build_invariant_flow_graph(&cluster.oracle_name, &flow_index, &params)
        })
        .collect();

    let graph_data = GraphData {
        graph_name: graph_name.to_string(),
        label: label.to_string(),
        width: total_width,
        height: max_height,
        clusters,
        invariant_flows,
    };

    let json = graph_data.to_json().replace("</", "<\\/");

    TEMPLATE
        .replace("__TITLE__", &html_escape(label))
        .replace("__GRAPH_DATA_JSON__", &json)
}

const TEMPLATE: &str = include_str!("template.html");

#[cfg(test)]
mod tests {
    use super::*;

    fn claim(name: &str, deps: &[&str], scope: Option<&[&str]>) -> Claim {
        Claim::from_tuple((
            name.to_string(),
            deps.iter().map(|s| s.to_string()).collect(),
            false,
            true,
            scope.map(|s| s.iter().map(|x| x.to_string()).collect()),
        ))
    }

    fn ctr_eq_source() -> ClaimSource {
        ClaimSource {
            kind: claim_source::ClaimKind::StateRelation,
            domino_source: "(define-state-relation ctr-eq (L R) (= L.A.ctr R.B.ctr))".to_string(),
            depends_on_new_state: false,
            easycrypt_source: "L.A.ctr = R.B.ctr".to_string(),
        }
    }

    #[test]
    fn undeclared_fragment_still_gets_a_real_invariant_node_with_a_scope_edge() {
        let params = LayoutParams::default();
        let tree = vec![
            claim("same-output", &["no-abort"], Some(&["ctr-eq"])),
            claim("equal-aborts", &[], None),
        ];
        let mut sources = BTreeMap::new();
        sources.insert("ctr-eq".to_string(), ctr_eq_source());

        let cluster = build_cluster("A", "B", "Test", &tree, Some(&sources), &params);

        let ctr_eq = cluster
            .nodes
            .iter()
            .find(|n| n.name == "ctr-eq")
            .expect("ctr-eq should be synthesized as a real node");
        assert!(
            !ctr_eq.implicit,
            "an auto-generated invariant fragment is a real proof obligation, not an undeclared stub"
        );
        assert_eq!(ctr_eq.claim_type, "Invariant");

        let edge = cluster
            .edges
            .iter()
            .find(|e| e.from == "Test::same-output" && e.to == ctr_eq.id)
            .expect("same-output should have a with-invariants edge to ctr-eq");
        assert_eq!(edge.kind, EdgeKind::WithInvariants);
    }

    #[test]
    fn plain_dependencies_are_unaffected() {
        let params = LayoutParams::default();
        let tree = vec![claim("same-output", &["no-abort"], None)];
        let cluster = build_cluster("A", "B", "Test", &tree, None, &params);
        let edge = cluster
            .edges
            .iter()
            .find(|e| e.from == "Test::same-output" && e.to == "Test::no-abort")
            .expect("plain dependency edge");
        assert_eq!(edge.kind, EdgeKind::Dependency);
    }

    #[test]
    fn self_referential_fragment_in_flow_graph_terminates_with_back_edge() {
        let params = LayoutParams::default();
        let mut sources = BTreeMap::new();
        sources.insert("ctr-eq".to_string(), ctr_eq_source());

        let test_tree = vec![
            claim("same-output", &["no-abort"], Some(&["ctr-eq"])),
            claim("equal-aborts", &[], None),
        ];
        // "Other" oracle's own claim for the shared fragment scopes right
        // back to itself -- an immediate cycle once the flow view starts
        // following cross-oracle candidates for "ctr-eq".
        let other_tree = vec![claim("ctr-eq", &[], Some(&["ctr-eq"]))];

        let clusters = vec![
            build_cluster("A", "B", "Test", &test_tree, Some(&sources), &params),
            build_cluster("A", "B", "Other", &other_tree, Some(&sources), &params),
        ];

        let index = FlowIndex::build(&clusters);
        // Terminating at all (this call returning) is half of what's under
        // test; an unguarded recursion here would hang or blow the stack.
        let flow = build_invariant_flow_graph("Test", &index, &params).expect("flow graph");

        assert!(
            flow.cross_edges.iter().any(|e| e.kind == EdgeKind::Back),
            "the self-referential fragment must be cut with a Back edge, not expanded forever"
        );
        assert!(
            flow.cross_edges
                .iter()
                .any(|e| e.kind == EdgeKind::CrossOracle && e.label.as_deref() == Some("Other")),
            "Test's ctr-eq should still jump into Other's independent proof of the same fragment"
        );
    }

    #[test]
    fn unrelated_branch_reaching_the_same_target_gets_its_own_expansion() {
        // Ancestor-based cycle detection (as opposed to a global
        // once-per-(oracle,fragment) cache): "Other::ctr-eq" is reachable
        // two different ways here --
        //   Test::ctr-eq --cross-oracle--> Other::ctr-eq                 (direct)
        //   Test::ctr-nonneg --cross-oracle--> Mid::ctr-nonneg
        //     --with-invariants--> Mid::ctr-eq --cross-oracle--> Other::ctr-eq  (via Mid)
        // and neither path is an ancestor of the other (they split at the
        // Test root, into same-output vs equal-aborts), so both must expand
        // Other::ctr-eq independently rather than the second one collapsing
        // into the first.
        let params = LayoutParams::default();
        let source = |name: &str| ClaimSource {
            kind: claim_source::ClaimKind::StateRelation,
            domino_source: format!("(define-state-relation {name} (L R) true)"),
            depends_on_new_state: false,
            easycrypt_source: "true".to_string(),
        };

        let mut test_sources = BTreeMap::new();
        test_sources.insert("ctr-eq".to_string(), source("ctr-eq"));
        test_sources.insert("ctr-nonneg".to_string(), source("ctr-nonneg"));
        let test_tree = vec![
            claim("same-output", &[], Some(&["ctr-eq"])),
            claim("equal-aborts", &[], Some(&["ctr-nonneg"])),
        ];

        let mut mid_sources = BTreeMap::new();
        mid_sources.insert("ctr-nonneg".to_string(), source("ctr-nonneg"));
        mid_sources.insert("ctr-eq".to_string(), source("ctr-eq"));
        let mid_tree = vec![claim("ctr-nonneg", &[], Some(&["ctr-eq"]))];

        let mut other_sources = BTreeMap::new();
        other_sources.insert("ctr-eq".to_string(), source("ctr-eq"));
        let other_tree = vec![claim("ctr-eq", &[], None)];

        let clusters = vec![
            build_cluster("A", "B", "Test", &test_tree, Some(&test_sources), &params),
            build_cluster("A", "B", "Mid", &mid_tree, Some(&mid_sources), &params),
            build_cluster(
                "A",
                "B",
                "Other",
                &other_tree,
                Some(&other_sources),
                &params,
            ),
        ];

        let index = FlowIndex::build(&clusters);
        let flow = build_invariant_flow_graph("Test", &index, &params).expect("flow graph");

        let other_targets: BTreeSet<&str> = flow
            .cross_edges
            .iter()
            .filter(|e| e.kind == EdgeKind::CrossOracle && e.label.as_deref() == Some("Other"))
            .map(|e| e.to.as_str())
            .collect();
        assert_eq!(
            other_targets.len(),
            2,
            "the two unrelated paths into Other::ctr-eq should produce two distinct flow nodes, not share one: {:?}",
            flow.cross_edges
        );
        assert_eq!(
            flow.clusters
                .iter()
                .filter(|c| c.oracle_name == "Other")
                .count(),
            2,
            "each independent jump into Other should get its own cluster"
        );
    }

    #[test]
    fn nested_cross_oracle_jump_back_into_an_active_ancestor_terminates() {
        // Regression test for a stack overflow found on a real project:
        // `branch_cross_oracle` only checked candidates against `ancestors`,
        // never its own `(from_oracle, fragment_name)` key on entry. Two
        // independent cross-oracle jumps (each with their own fresh
        // `local_memo`, so local same-cluster memoization can't see each
        // other) could both walk back into the very same ancestor pair and
        // re-enter `branch_cross_oracle` for it while it was still on the
        // call stack, re-pushing the same key and recursing forever instead
        // of stopping with a `Back` edge:
        //   Root::same-output --w/inv--> Root::F --w/inv--> Root::G
        //     --cross-oracle--> A::G --w/inv--> A::F --w/inv--> A::G (local cycle, fine)
        //     A::G --cross-oracle--> A::F's own w/inv jump back to Root::F
        //       --w/inv--> Root::G  <-- same (Root, G) pair already an
        //                              ancestor, reached via a fresh
        //                              `local_memo`/candidate loop that
        //                              can't see the outer one.
        let params = LayoutParams::default();
        let source = |name: &str| ClaimSource {
            kind: claim_source::ClaimKind::StateRelation,
            domino_source: format!("(define-state-relation {name} (L R) true)"),
            depends_on_new_state: false,
            easycrypt_source: "true".to_string(),
        };
        let mut sources = BTreeMap::new();
        sources.insert("F".to_string(), source("F"));
        sources.insert("G".to_string(), source("G"));

        let root_tree = vec![
            claim("same-output", &[], Some(&["F"])),
            claim("F", &[], Some(&["G"])),
            claim("G", &[], None),
        ];
        let a_tree = vec![
            claim("F", &[], Some(&["G"])),
            claim("G", &[], Some(&["F"])),
        ];

        let clusters = vec![
            build_cluster("L", "R", "Root", &root_tree, Some(&sources), &params),
            build_cluster("L", "R", "A", &a_tree, Some(&sources), &params),
        ];

        let index = FlowIndex::build(&clusters);
        // Terminating at all (this call returning instead of hanging or
        // overflowing the stack) is what's under test.
        let flow = build_invariant_flow_graph("Root", &index, &params).expect("flow graph");

        assert!(
            flow.cross_edges.iter().any(|e| e.kind == EdgeKind::Back),
            "the reentrant (Root, G) ancestor pair must be cut with a Back edge: {:?}",
            flow.cross_edges
        );
    }
}
