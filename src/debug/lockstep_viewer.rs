// SPDX-License-Identifier: MIT OR Apache-2.0

//! The joint-tree viewer of a lockstep run (`docs/stories/easycrypt/24-joint-tree-viewer.md`):
//! the self-contained `index.html` `domino debug --easycrypt` writes.
//!
//! Like the sequential viewer ([`crate::debug::report`]) the page is a renderer
//! over `trace.json`: the trace is embedded verbatim in a
//! `<script type="application/json">` block, all CSS and JS are inline, and the
//! page fetches nothing, so it opens from `file://` offline. Two things are
//! added to the trace:
//!
//! * the **stuck-point rollups** ([`stuck_rollups`]), the Domino verdicts of
//!   every joint path below each stuck point, computed here rather than in the
//!   page so a test can check them against `trace.json` independently;
//! * for a run in progress, `<meta http-equiv="refresh" content="2">`. A browser
//!   blocks `fetch` of local files, so reloading the page is the only way a
//!   `file://` page can follow a run. The final write omits the tag.
//!
//! The page is a pure function of its inputs: two runs of an unchanged project
//! produce byte-identical files.

use std::collections::BTreeMap;

use serde_derive::Serialize;

use crate::debug::driver::ClaimInfo;
use crate::debug::lockstep::{ChildOutcome, LockstepOutcome, PairRecord};
use crate::debug::lockstep_run::{ClaimCounts, VerdictCounts};
use crate::debug::report::{EFFECT_JS, VIEWER_CSS};

/// What the Domino verdicts say about everything below one stuck point: how
/// many joint paths lie below it, how each claim fared on them, and which state
/// relations failed where. It answers "is this admit verified in Domino, or
/// inconclusive there too".
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StuckRollup {
    /// `S<n>`.
    pub id: String,
    /// Joint paths in the subtree of the stuck point's node, found so far.
    pub pairs: usize,
    /// How each claim fared on them, in the order the run checks the claims.
    pub claims: Vec<ClaimCounts>,
    /// Per state relation, the joint paths where it failed or was
    /// inconclusive, by relation name.
    pub relations: Vec<RelationRollup>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RelationRollup {
    pub name: String,
    pub failing: Vec<RelationFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RelationFailure {
    /// The joint path, `J<n>`.
    pub pair: String,
    /// `goal-fails` or `inconclusive`.
    pub verdict: &'static str,
}

/// One rollup per stuck point, in the order of [`LockstepOutcome::stuck`].
pub fn stuck_rollups(outcome: &LockstepOutcome, claims: &[ClaimInfo]) -> Vec<StuckRollup> {
    let pairs_by_id: BTreeMap<&str, &PairRecord> =
        outcome.pairs.iter().map(|p| (p.id.as_str(), p)).collect();
    outcome
        .stuck
        .iter()
        .map(|stuck| {
            let mut below: Vec<&PairRecord> = Vec::new();
            let mut todo = vec![stuck.node];
            while let Some(index) = todo.pop() {
                let Some(node) = outcome.tree.nodes.get(index) else {
                    continue;
                };
                if let Some(pair) = node.pair.as_deref().and_then(|id| pairs_by_id.get(id)) {
                    below.push(pair);
                }
                for child in &node.children {
                    if let ChildOutcome::Explored { node } = child.outcome {
                        todo.push(node);
                    }
                }
            }
            // The traversal order is a stack's; ids are depth-first order.
            below.sort_by_key(|p| p.node);

            let mut rollup = StuckRollup {
                id: stuck.id.clone(),
                pairs: below.len(),
                claims: claims
                    .iter()
                    .filter(|c| !c.admitted)
                    .map(|c| ClaimCounts {
                        claim: c.name.clone(),
                        counts: VerdictCounts::default(),
                    })
                    .collect(),
                relations: Vec::new(),
            };
            let mut by_relation: BTreeMap<&str, Vec<RelationFailure>> = BTreeMap::new();
            for pair in below {
                for c in &mut rollup.claims {
                    if let Some(verdict) = pair.verdict_of(&c.claim) {
                        c.counts.bump(verdict);
                    }
                }
                for r in pair.relations().iter().filter(|r| r.verdict.is_failure()) {
                    by_relation.entry(&r.name).or_default().push(RelationFailure {
                        pair: pair.id.clone(),
                        verdict: r.verdict.slug(),
                    });
                }
            }
            rollup.relations = by_relation
                .into_iter()
                .map(|(name, failing)| RelationRollup {
                    name: name.to_string(),
                    failing,
                })
                .collect();
            rollup
        })
        .collect()
}

/// The page for `trace_json` (the `trace.json` text) and `rollups`. `live` is
/// true while the run is in progress: the page then reloads itself every two
/// seconds.
pub fn render_html(trace_json: &str, rollups: &[StuckRollup], live: bool) -> String {
    let rollups_json = serde_json::to_string(rollups).unwrap_or_else(|_| "[]".to_string());
    // Every `<` in valid JSON is inside a string literal, so escaping it keeps
    // the JSON identical while making a `</script>` breakout impossible.
    let escape = |json: &str| json.replace('<', "\\u003c");
    TEMPLATE
        .replace("__REFRESH__", if live { REFRESH_TAG } else { "" })
        .replace("__VIEWER_CSS__", VIEWER_CSS)
        .replace("__EFFECT_JS__", EFFECT_JS)
        .replace("__ROLLUPS_JSON__", &escape(&rollups_json))
        .replace("__TRACE_JSON__", &escape(trace_json))
}

/// The tag a page in progress carries; the final page has none.
pub(crate) const REFRESH_TAG: &str = "<meta http-equiv=\"refresh\" content=\"2\">\n";

/// Remove the refresh tag from an `index.html` already on disk. Used when a run
/// dies before its final write, so the page does not reload forever.
pub(crate) fn without_refresh(page: &str) -> String {
    page.replacen(REFRESH_TAG, "", 1)
}

const TEMPLATE: &str = include_str!("lockstep_viewer.html");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::debug::driver::{ClaimVerdict, StopReason, TerminalView, Verdict};
    use crate::debug::lockstep::{
        HeadKind, HeadView, JointChild, JointNode, JointTree, NodeKind, PairSide, RelationVerdict,
        SideStep, SideView, StuckPoint, StuckReason,
    };

    fn side() -> SideView {
        SideView {
            head: HeadView {
                kind: HeadKind::Return,
                label: 1,
            },
            consumed: Vec::new(),
            plumbing: None,
        }
    }

    fn node(index: usize, children: &[Option<usize>]) -> JointNode {
        JointNode {
            index,
            kind: NodeKind::Split,
            left: side(),
            right: side(),
            answers: Vec::new(),
            children: children
                .iter()
                .map(|c| JointChild {
                    left: Some(SideStep {
                        label: 1,
                        decision: "then".to_string(),
                    }),
                    right: None,
                    outcome: match c {
                        Some(node) => ChildOutcome::Explored { node: *node },
                        None => ChildOutcome::NotExplored,
                    },
                })
                .collect(),
            pair: None,
            stuck: None,
        }
    }

    fn pair(
        id: &str,
        node: usize,
        equal_output: Verdict,
        invariant: Verdict,
        relations: &[(&str, Verdict)],
    ) -> PairRecord {
        let side = || PairSide {
            steps: Vec::new(),
            terminal: TerminalView {
                label: 1,
                line: String::new(),
                is_abort: false,
            },
            lines: Vec::new(),
            effect: None,
        };
        PairRecord {
            id: id.to_string(),
            node,
            left: side(),
            right: side(),
            claims: vec![
                ClaimVerdict {
                    claim: "equal-output".to_string(),
                    verdict: equal_output,
                    relations: Vec::new(),
                },
                ClaimVerdict {
                    claim: "invariant".to_string(),
                    verdict: invariant,
                    relations: relations
                        .iter()
                        .map(|(name, verdict)| RelationVerdict {
                            name: name.to_string(),
                            verdict: verdict.clone(),
                        })
                        .collect(),
                },
            ],
        }
    }

    fn claims() -> Vec<ClaimInfo> {
        ["equal-output", "invariant"]
            .iter()
            .map(|name| ClaimInfo {
                name: name.to_string(),
                dependencies: Vec::new(),
                admitted: false,
            })
            .collect()
    }

    fn counts<'a>(rollup: &'a StuckRollup, claim: &str) -> &'a VerdictCounts {
        &rollup.claims.iter().find(|c| c.claim == claim).unwrap().counts
    }

    fn stuck(id: &str, node: usize) -> StuckPoint {
        StuckPoint {
            id: id.to_string(),
            node,
            side: "left",
            label: 1,
            left_label: 1,
            right_label: 1,
            sample: "P.O.x".to_string(),
            draw: 0,
            reason: StuckReason::PartnerNotAtHead,
        }
    }

    /// Node 0 -> 1 (S1) -> {2 (J1), 3 -> {4 (J2), 5 (J3)}}; node 6 (J4) hangs
    /// off node 0 next to node 1 and is not below S1. Node 3 is S2.
    fn outcome() -> LockstepOutcome {
        let mut nodes = vec![
            node(0, &[Some(1), Some(6)]),
            node(1, &[Some(2), Some(3)]),
            node(2, &[]),
            node(3, &[Some(4), Some(5), None]),
            node(4, &[]),
            node(5, &[]),
            node(6, &[]),
        ];
        for (n, id) in [(2, "J1"), (4, "J2"), (5, "J3"), (6, "J4")] {
            nodes[n].pair = Some(id.to_string());
            nodes[n].kind = NodeKind::TerminalPair;
        }
        let fails = |m: &str| Verdict::GoalFails {
            model: format!("models/{m}.smt2"),
        };
        let unknown = Verdict::Inconclusive { model: None };
        LockstepOutcome {
            tree: JointTree { nodes },
            pairs: vec![
                pair("J1", 2, Verdict::Verified, Verdict::Verified, &[]),
                pair(
                    "J2",
                    4,
                    Verdict::Verified,
                    fails("J2.invariant"),
                    &[
                        ("rel_a", Verdict::Verified),
                        ("rel_b", fails("J2.relation-rel_b")),
                    ],
                ),
                pair(
                    "J3",
                    5,
                    Verdict::pair_infeasible(),
                    unknown.clone(),
                    &[("rel_b", unknown), ("rel_a", fails("J3.relation-rel_a"))],
                ),
                pair("J4", 6, fails("J4.equal-output"), Verdict::Verified, &[]),
            ],
            stuck: vec![stuck("S1", 1), stuck("S2", 3)],
            stop_reason: StopReason::Completed,
        }
    }

    #[test]
    fn a_rollup_counts_the_joint_paths_below_the_stuck_point_only() {
        let rollups = stuck_rollups(&outcome(), &claims());
        let s1 = &rollups[0];
        assert_eq!(s1.id, "S1");
        assert_eq!(s1.pairs, 3, "J4 is beside the stuck point, not below it");
        assert_eq!(counts(s1, "equal-output").verified, 2);
        assert_eq!(counts(s1, "equal-output").unreachable, 1);
        assert_eq!(counts(s1, "invariant").verified, 1);
        assert_eq!(counts(s1, "invariant").goal_fails, 1);
        assert_eq!(counts(s1, "invariant").inconclusive, 1);

        let s2 = &rollups[1];
        assert_eq!((s2.id.as_str(), s2.pairs), ("S2", 2));
    }

    #[test]
    fn a_rollup_names_the_failing_relations_and_where() {
        let s1 = &stuck_rollups(&outcome(), &claims())[0];
        let names: Vec<(&str, Vec<(&str, &str)>)> = s1
            .relations
            .iter()
            .map(|r| {
                (
                    r.name.as_str(),
                    r.failing
                        .iter()
                        .map(|f| (f.pair.as_str(), f.verdict))
                        .collect(),
                )
            })
            .collect();
        assert_eq!(
            names,
            vec![
                ("rel_a", vec![("J3", "goal-fails")]),
                ("rel_b", vec![("J2", "goal-fails"), ("J3", "inconclusive")]),
            ],
            "verified relations are not listed; failures are in joint-path order"
        );
    }

    #[test]
    fn a_stuck_point_with_nothing_below_it_yet_rolls_up_to_nothing() {
        let mut o = outcome();
        o.tree.nodes[3].children.clear();
        o.pairs.retain(|p| p.id != "J2" && p.id != "J3");
        let s2 = &stuck_rollups(&o, &claims())[1];
        assert_eq!(s2.pairs, 0);
        assert_eq!(*counts(s2, "invariant"), VerdictCounts::default());
        assert!(s2.relations.is_empty());
    }

    #[test]
    fn a_pair_node_whose_record_is_not_written_yet_is_ignored() {
        let mut o = outcome();
        o.pairs.retain(|p| p.id != "J1");
        assert_eq!(stuck_rollups(&o, &claims())[0].pairs, 2);
    }

    #[test]
    fn only_a_page_in_progress_refreshes_itself() {
        let live = render_html("{}", &[], true);
        let done = render_html("{}", &[], false);
        assert!(live.contains(REFRESH_TAG));
        assert!(!done.contains("<meta http-equiv"), "the final page must not refresh");
        assert_eq!(without_refresh(&live), done);
    }

    #[test]
    fn the_embedded_json_cannot_close_its_script_block() {
        let page = render_html(r#"{"line":"</script><b>"}"#, &[], false);
        assert!(!page.contains("</script><b>"));
        assert!(page.contains("\\u003c/script>"));
    }

    #[test]
    fn rendering_is_a_pure_function_of_its_inputs() {
        let a = render_html("{}", &stuck_rollups(&outcome(), &claims()), false);
        let b = render_html("{}", &stuck_rollups(&outcome(), &claims()), false);
        assert_eq!(a, b);
    }
}
