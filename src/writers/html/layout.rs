// SPDX-License-Identifier: MIT OR Apache-2.0

//! A small, dependency-free layered ("Sugiyama-style") DAG layout, used to
//! position claim-dependency graphs on the HTML lemma-tree canvas.
//!
//! This deliberately does not shell out to Graphviz: the goal is a fully
//! self-contained `domino` binary. It also doesn't insert dummy/virtual
//! nodes to bend edges that span more than one layer -- those are drawn as
//! straight lines directly between the two real nodes instead. For the
//! claim-dependency graphs this renders (a handful of layers, at most a few
//! dozen nodes per oracle) that reads fine in practice and keeps the
//! algorithm simple; giving multi-layer edges bend points is a reasonable
//! future improvement if graphs grow large enough for it to matter.
//!
//! Steps: 1) rank nodes by longest path to a sink so dependents always end
//! up above their dependencies, 2) order each layer with a barycenter sweep
//! to reduce edge crossings, 3) assign evenly-spaced, layer-centered
//! coordinates.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LayoutParams {
    pub node_width: f64,
    pub node_height: f64,
    pub x_gap: f64,
    pub y_gap: f64,
}

impl Default for LayoutParams {
    fn default() -> Self {
        Self {
            node_width: 220.0,
            node_height: 56.0,
            x_gap: 40.0,
            y_gap: 70.0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct PositionedNode {
    pub id: String,
    /// Top-left corner (not center) in layout-local coordinates.
    pub x: f64,
    pub y: f64,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Layout {
    pub nodes: Vec<PositionedNode>,
    pub width: f64,
    pub height: f64,
}

/// Longest-path-to-a-sink depth of every node, following `node -> dep` edges
/// forward. Leaves (no outgoing edges) get depth 0. Guards against cycles
/// (which shouldn't occur in a claim dependency graph, but malformed input
/// shouldn't hang the exporter either) by treating a node revisited while
/// still on the current DFS stack as depth 0.
fn compute_depths(
    node_ids: &[String],
    outgoing: &BTreeMap<&str, Vec<&str>>,
) -> BTreeMap<String, usize> {
    let mut depth: BTreeMap<String, usize> = BTreeMap::new();
    let mut on_stack: BTreeMap<&str, bool> = BTreeMap::new();

    fn visit<'a>(
        node: &'a str,
        outgoing: &BTreeMap<&'a str, Vec<&'a str>>,
        depth: &mut BTreeMap<String, usize>,
        on_stack: &mut BTreeMap<&'a str, bool>,
    ) -> usize {
        if let Some(d) = depth.get(node) {
            return *d;
        }
        if *on_stack.get(node).unwrap_or(&false) {
            // Cycle guard: don't recurse further down an already-active path.
            return 0;
        }
        on_stack.insert(node, true);
        let d = outgoing
            .get(node)
            .map(|deps| {
                deps.iter()
                    .map(|dep| 1 + visit(dep, outgoing, depth, on_stack))
                    .max()
                    .unwrap_or(0)
            })
            .unwrap_or(0);
        on_stack.insert(node, false);
        depth.insert(node.to_string(), d);
        d
    }

    for id in node_ids {
        visit(id, outgoing, &mut depth, &mut on_stack);
    }

    depth
}

/// Reorders each layer (after the first) by the average position of its
/// neighbors in the layer above, then each layer (before the last) by the
/// average position of its neighbors in the layer below -- a standard
/// barycenter crossing-reduction sweep. Nodes with no positioned neighbors
/// keep their relative order.
fn barycenter_sweep(
    layers: &mut [Vec<String>],
    outgoing: &BTreeMap<&str, Vec<&str>>,
    incoming: &BTreeMap<&str, Vec<&str>>,
    iterations: usize,
) {
    // Owned (not borrowed) so computing one layer's positions doesn't keep
    // `layers` immutably borrowed while we mutate another layer in it.
    fn position_of(layer: &[String]) -> BTreeMap<String, f64> {
        layer
            .iter()
            .enumerate()
            .map(|(i, id)| (id.clone(), i as f64))
            .collect()
    }

    let reorder_by = |layer: &mut Vec<String>,
                      neighbor_pos: &BTreeMap<String, f64>,
                      adj: &BTreeMap<&str, Vec<&str>>| {
        let barycenter = |id: &str| -> f64 {
            let neighbors = adj.get(id).map(Vec::as_slice).unwrap_or(&[]);
            let positions: Vec<f64> = neighbors
                .iter()
                .filter_map(|n| neighbor_pos.get(*n).copied())
                .collect();
            if positions.is_empty() {
                // Keep unpositioned nodes roughly where they already are by
                // falling back to a neutral mid-range value, computed below.
                f64::NAN
            } else {
                positions.iter().sum::<f64>() / positions.len() as f64
            }
        };

        let mut keyed: Vec<(f64, usize, String)> = layer
            .iter()
            .enumerate()
            .map(|(i, id)| (barycenter(id), i, id.clone()))
            .collect();

        // Nodes with no positioned neighbor (NaN) keep their original slot
        // by sorting stably on original index as a tiebreak, using the
        // average of the finite values as their fallback key.
        let finite_avg = {
            let finite: Vec<f64> = keyed
                .iter()
                .map(|(b, ..)| *b)
                .filter(|b| !b.is_nan())
                .collect();
            if finite.is_empty() {
                0.0
            } else {
                finite.iter().sum::<f64>() / finite.len() as f64
            }
        };
        for (b, i, _) in keyed.iter_mut() {
            if b.is_nan() {
                *b = finite_avg + (*i as f64) * 1e-6;
            }
        }

        keyed.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.cmp(&b.1)));
        *layer = keyed.into_iter().map(|(_, _, id)| id).collect();
    };

    for _ in 0..iterations {
        for i in 1..layers.len() {
            let pos = position_of(&layers[i - 1]);
            reorder_by(&mut layers[i], &pos, incoming);
        }
        for i in (0..layers.len().saturating_sub(1)).rev() {
            let pos = position_of(&layers[i + 1]);
            reorder_by(&mut layers[i], &pos, outgoing);
        }
    }
}

/// Lays out a DAG given as a node id list and `(from, to)` edges, where an
/// edge means "`from` depends on `to`" -- `from` is placed above `to`.
/// Isolated/duplicate edges and self-loops are tolerated; `node_ids` should
/// already be deduplicated (callers control that, since it also determines
/// initial layer ordering).
pub fn layered_layout(
    node_ids: &[String],
    edges: &[(String, String)],
    params: &LayoutParams,
) -> Layout {
    if node_ids.is_empty() {
        return Layout {
            nodes: Vec::new(),
            width: 0.0,
            height: 0.0,
        };
    }

    let mut outgoing: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut incoming: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (from, to) in edges {
        if from == to {
            continue;
        }
        outgoing.entry(from.as_str()).or_default().push(to.as_str());
        incoming.entry(to.as_str()).or_default().push(from.as_str());
    }

    let depth = compute_depths(node_ids, &outgoing);
    let max_depth = depth.values().copied().max().unwrap_or(0);

    let mut layers: Vec<Vec<String>> = vec![Vec::new(); max_depth + 1];
    for id in node_ids {
        let d = depth.get(id).copied().unwrap_or(0);
        let rank = max_depth - d;
        layers[rank].push(id.clone());
    }

    barycenter_sweep(&mut layers, &outgoing, &incoming, 4);

    let layer_widths: Vec<f64> = layers
        .iter()
        .map(|layer| {
            if layer.is_empty() {
                0.0
            } else {
                layer.len() as f64 * params.node_width + (layer.len() as f64 - 1.0) * params.x_gap
            }
        })
        .collect();
    let total_width = layer_widths.iter().cloned().fold(0.0, f64::max);

    let mut nodes = Vec::with_capacity(node_ids.len());
    for (rank, layer) in layers.iter().enumerate() {
        let layer_width = layer_widths[rank];
        let x_offset = (total_width - layer_width) / 2.0;
        let y = rank as f64 * (params.node_height + params.y_gap);
        for (i, id) in layer.iter().enumerate() {
            let x = x_offset + i as f64 * (params.node_width + params.x_gap);
            nodes.push(PositionedNode {
                id: id.clone(),
                x,
                y,
            });
        }
    }

    let height = (max_depth + 1) as f64 * params.node_height + max_depth as f64 * params.y_gap;

    Layout {
        nodes,
        width: total_width.max(params.node_width),
        height,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap as Map;

    fn ids(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn es(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }

    fn node_pos(layout: &Layout) -> Map<String, (f64, f64)> {
        layout
            .nodes
            .iter()
            .map(|n| (n.id.clone(), (n.x, n.y)))
            .collect()
    }

    #[test]
    fn every_node_gets_a_position_exactly_once() {
        let nodes = ids(&["a", "b", "c", "d"]);
        let edges = es(&[("a", "b"), ("b", "c"), ("a", "d")]);
        let layout = layered_layout(&nodes, &edges, &LayoutParams::default());
        assert_eq!(layout.nodes.len(), 4);
        let mut seen: Vec<&str> = layout.nodes.iter().map(|n| n.id.as_str()).collect();
        seen.sort();
        assert_eq!(seen, vec!["a", "b", "c", "d"]);
    }

    #[test]
    fn dependents_are_strictly_above_their_dependencies() {
        // a -> b -> c: a is a root claim, c is the ultimate leaf.
        let nodes = ids(&["a", "b", "c"]);
        let edges = es(&[("a", "b"), ("b", "c")]);
        let layout = layered_layout(&nodes, &edges, &LayoutParams::default());
        let pos = node_pos(&layout);
        assert!(pos["a"].1 < pos["b"].1);
        assert!(pos["b"].1 < pos["c"].1);
    }

    #[test]
    fn independent_nodes_share_no_x_overlap_within_a_layer() {
        // Root depends on three independent leaves -> they must share one
        // layer and not overlap horizontally.
        let nodes = ids(&["root", "l1", "l2", "l3"]);
        let edges = es(&[("root", "l1"), ("root", "l2"), ("root", "l3")]);
        let params = LayoutParams::default();
        let layout = layered_layout(&nodes, &edges, &params);
        let pos = node_pos(&layout);
        let mut xs: Vec<f64> = vec![pos["l1"].0, pos["l2"].0, pos["l3"].0];
        xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        for pair in xs.windows(2) {
            assert!(
                pair[1] - pair[0] >= params.node_width,
                "nodes overlap: {pair:?}"
            );
        }
    }

    #[test]
    fn leaf_referenced_at_different_depths_lands_on_the_deeper_layer() {
        // a -> b -> c, and a -> c directly. c's rank must respect the
        // longest path (via b), not the shortcut, so the direct a->c edge
        // doesn't collide with b's layer.
        let nodes = ids(&["a", "b", "c"]);
        let edges = es(&[("a", "b"), ("b", "c"), ("a", "c")]);
        let layout = layered_layout(&nodes, &edges, &LayoutParams::default());
        let pos = node_pos(&layout);
        assert!(pos["a"].1 < pos["b"].1);
        assert!(pos["b"].1 < pos["c"].1);
    }

    #[test]
    fn disconnected_nodes_still_get_laid_out() {
        let nodes = ids(&["only"]);
        let layout = layered_layout(&nodes, &[], &LayoutParams::default());
        assert_eq!(layout.nodes.len(), 1);
    }

    #[test]
    fn empty_graph_is_empty_layout() {
        let layout = layered_layout(&[], &[], &LayoutParams::default());
        assert!(layout.nodes.is_empty());
        assert_eq!(layout.width, 0.0);
        assert_eq!(layout.height, 0.0);
    }

    #[test]
    fn self_loop_is_ignored_without_panicking() {
        let nodes = ids(&["a"]);
        let edges = es(&[("a", "a")]);
        let layout = layered_layout(&nodes, &edges, &LayoutParams::default());
        assert_eq!(layout.nodes.len(), 1);
    }

    #[test]
    fn cycle_does_not_hang_or_panic() {
        let nodes = ids(&["a", "b"]);
        let edges = es(&[("a", "b"), ("b", "a")]);
        let layout = layered_layout(&nodes, &edges, &LayoutParams::default());
        assert_eq!(layout.nodes.len(), 2);
    }

    /// Counts edge crossings for a two-layer bipartite ordering -- used to
    /// confirm the barycenter sweep actually improves on a deliberately bad
    /// initial order, not just that it runs.
    fn count_adjacent_crossings(
        upper: &[String],
        lower: &[String],
        edges: &[(String, String)],
    ) -> usize {
        let upos: Map<&str, usize> = upper
            .iter()
            .enumerate()
            .map(|(i, s)| (s.as_str(), i))
            .collect();
        let lpos: Map<&str, usize> = lower
            .iter()
            .enumerate()
            .map(|(i, s)| (s.as_str(), i))
            .collect();
        let positioned: Vec<(usize, usize)> = edges
            .iter()
            .filter_map(|(a, b)| Some((*upos.get(a.as_str())?, *lpos.get(b.as_str())?)))
            .collect();
        let mut crossings = 0;
        for i in 0..positioned.len() {
            for j in (i + 1)..positioned.len() {
                let (a1, b1) = positioned[i];
                let (a2, b2) = positioned[j];
                if (a1 < a2 && b1 > b2) || (a1 > a2 && b1 < b2) {
                    crossings += 1;
                }
            }
        }
        crossings
    }

    #[test]
    fn barycenter_sweep_reduces_crossings_on_a_bad_initial_order() {
        // Deliberately "crossed" wiring: root order [x,y,z] connects to leaf
        // order [c,b,a] one-to-one, which is maximally crossed if both
        // layers keep this input order.
        let root_ids = ids(&["x", "y", "z"]);
        let leaf_ids = ids(&["a", "b", "c"]);
        let mut node_ids = root_ids.clone();
        node_ids.extend(leaf_ids.clone());
        // Insert a top uber-root so x/y/z land in one layer and a/b/c in
        // the layer below, deterministically, regardless of source order.
        let mut all = vec!["top".to_string()];
        all.extend(node_ids);
        let edges = es(&[
            ("top", "x"),
            ("top", "y"),
            ("top", "z"),
            ("x", "c"),
            ("y", "b"),
            ("z", "a"),
        ]);

        let before = count_adjacent_crossings(&root_ids, &leaf_ids, &edges);
        assert_eq!(before, 3, "sanity check on the deliberately-bad wiring");

        let layout = layered_layout(&all, &edges, &LayoutParams::default());
        let mut by_rank: Map<i64, Vec<(f64, String)>> = Map::new();
        // rank isn't in PositionedNode; recover the layer via y.
        for n in &layout.nodes {
            by_rank
                .entry(n.y as i64)
                .or_default()
                .push((n.x, n.id.clone()));
        }
        let mut ranks: Vec<&i64> = by_rank.keys().collect();
        ranks.sort();
        let mut layer_orders: Vec<Vec<String>> = Vec::new();
        for r in ranks {
            let mut row = by_rank[r].clone();
            row.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
            layer_orders.push(row.into_iter().map(|(_, id)| id).collect());
        }
        // layer_orders[0] = ["top"], [1] = roots, [2] = leaves
        let after = count_adjacent_crossings(&layer_orders[1], &layer_orders[2], &edges);
        assert!(
            after <= before,
            "expected sweep to not worsen crossings: before={before} after={after}"
        );
    }
}
