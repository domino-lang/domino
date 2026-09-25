// SPDX-License-Identifier: MIT OR Apache-2.0

//! Alignment of decision skeletons (story 26 §3.3, ADR 0002).
//!
//! [`align`] walks EasyCrypt's skeleton and the IR's in parallel, so that each joint decision
//! of a lockstep execution can be tied to an instruction of the program EasyCrypt shows.
//!
//! - equal kinds match, and branches recurse into then and else;
//! - an IR end matches whatever EasyCrypt has left at that nesting level (the plumbing the
//!   closing step consumes);
//! - anything else is a [`Mismatch`], after which the walk resynchronises on the next pair of
//!   sub-skeletons that agree completely, so one surprise does not hide the rest.
//!
//! [`align_router`] first peels off the router: after `proc; inline.` the whole program of an
//! exported oracle is the router's `if (!abort_flag) { … }`, and only its body is compared.

use crate::debug::ir::{Label, Plumbing};

use super::skeleton::{Arm, EcPos, Node, NodeKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MismatchKind {
    /// Both sides have a decision here and they are of different kinds.
    KindDiffers,
    /// EasyCrypt has a decision the IR does not.
    ExtraEcDecision,
    /// The IR has a decision EasyCrypt does not.
    MissingEcDecision,
    /// EasyCrypt has an instruction alignment cannot classify (`while`, `match`, `call`, …).
    UnknownEcInstruction,
    /// The program is not the router's `if (!abort_flag) { … }` and nothing else.
    RouterShape,
}

impl MismatchKind {
    pub fn slug(self) -> &'static str {
        match self {
            MismatchKind::KindDiffers => "kind-differs",
            MismatchKind::ExtraEcDecision => "extra-ec-decision",
            MismatchKind::MissingEcDecision => "missing-ec-decision",
            MismatchKind::UnknownEcInstruction => "unknown-ec-instruction",
            MismatchKind::RouterShape => "router-shape",
        }
    }
}

/// One branch on the way from the root to a mismatch: the IR label of the `if`, and the arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathStep {
    pub ir_label: Label,
    pub arm: Arm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mismatch {
    pub kind: MismatchKind,
    /// The branches from the root down to where the mismatch is; empty at the top level.
    pub path: Vec<PathStep>,
    /// The EasyCrypt side: its `pp` (a condition or an instruction), if there is one.
    pub ec: Option<String>,
    pub ec_pos: Option<EcPos>,
    /// The IR side: a label and description, if there is one.
    pub ir: Option<String>,
}

/// The EasyCrypt instruction an IR decision was matched with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcInstr {
    pub pos: Option<EcPos>,
    /// The condition (branch) or the whole statement (sampling); empty for an end that swallowed
    /// nothing.
    pub pp: String,
    /// A sampling's target, as EasyCrypt prints it.
    pub lvalue: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecisionKind {
    Branch,
    Sampling,
    /// `EcInstr` is the first instruction the end swallowed, if any.
    End,
}

/// An IR decision and the EasyCrypt instruction it stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecisionMatch {
    pub ir_label: Label,
    pub kind: DecisionKind,
    pub plumbing: Option<Plumbing>,
    pub ec: EcInstr,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Alignment {
    /// In the order the walk found them (depth first, then before else).
    pub matches: Vec<DecisionMatch>,
    pub mismatches: Vec<Mismatch>,
}

impl Alignment {
    pub fn is_aligned(&self) -> bool {
        self.mismatches.is_empty()
    }

    /// The EasyCrypt instruction the IR decision `label` was matched with.
    pub fn ec_for(&self, label: Label) -> Option<&EcInstr> {
        self.matches
            .iter()
            .find(|m| m.ir_label == label)
            .map(|m| &m.ec)
    }
}

/// Aligns EasyCrypt's skeleton `ec` with the IR's `ir`.
pub fn align(ec: &[Node], ir: &[Node]) -> Alignment {
    let mut aligner = Aligner::default();
    aligner.lists(ec, ir, &mut Vec::new());
    aligner.out
}

/// Aligns a whole EasyCrypt program with the IR: the router's guard is peeled off first.
/// `abort_flag` is the router's abort flag as EasyCrypt prints it (`Comp_X.Game_X.abort_flag`,
/// known from `game.rs`, not read out of the output); the guard's condition must mention it.
pub fn align_router(ec: &[Node], ir: &[Node], abort_flag: &str) -> Alignment {
    let guard = match ec {
        [node @ Node {
            kind: NodeKind::Branch { then, els },
            ..
        }] if els.is_empty() && node.text.contains(abort_flag) => Some(then),
        _ => None,
    };
    let Some(body) = guard else {
        let described = if ec.is_empty() {
            "no decision at all".to_string()
        } else {
            ec.iter()
                .map(|n| n.text.as_str())
                .collect::<Vec<_>>()
                .join(" ; ")
        };
        return Alignment {
            matches: vec![],
            mismatches: vec![Mismatch {
                kind: MismatchKind::RouterShape,
                path: vec![],
                ec: Some(format!(
                    "expected a single `if (!{abort_flag}) {{ … }}`, found: {described}"
                )),
                ec_pos: ec.first().and_then(|n| n.pos.clone()),
                ir: None,
            }],
        };
    };
    let mut aligner = Aligner::default();
    aligner.lists(body, ir, &mut Vec::new());
    aligner.out
}

#[derive(Default)]
struct Aligner {
    out: Alignment,
}

fn describe_ir(node: &Node) -> String {
    let what = match node.kind {
        NodeKind::Branch { .. } => "branch",
        NodeKind::Sampling => "sampling",
        NodeKind::End => "end",
        NodeKind::Unknown => "unknown",
    };
    let plumbing = match node.plumbing {
        Some(Plumbing::DoneGuard) => " (done guard)",
        Some(Plumbing::CallResult) => " (call result)",
        None => "",
    };
    let label = node.label.map_or(String::new(), |l| format!(" @L{l}"));
    if node.text.is_empty() {
        format!("{what}{label}{plumbing}")
    } else {
        format!("{what}{label}{plumbing}: {}", node.text)
    }
}

fn same_kind(ec: &Node, ir: &Node) -> bool {
    matches!(
        (&ec.kind, &ir.kind),
        (NodeKind::Branch { .. }, NodeKind::Branch { .. })
            | (NodeKind::Sampling, NodeKind::Sampling)
    )
}

/// Whether `ec` and `ir` agree completely, with no mismatch and no resynchronisation.
fn strict_eq(ec: &Node, ir: &Node) -> bool {
    match (&ec.kind, &ir.kind) {
        (NodeKind::Branch { then: et, els: ee }, NodeKind::Branch { then: it, els: ie }) => {
            strict_lists(et, it) && strict_lists(ee, ie)
        }
        (NodeKind::Sampling, NodeKind::Sampling) => true,
        _ => false,
    }
}

fn strict_lists(ec: &[Node], ir: &[Node]) -> bool {
    let mut i = 0;
    for node in ir {
        if node.kind == NodeKind::End {
            return ec[i..].iter().all(|n| n.kind != NodeKind::Unknown);
        }
        if i >= ec.len() || !strict_eq(&ec[i], node) {
            return false;
        }
        i += 1;
    }
    i == ec.len()
}

/// The smallest pure insertion (`(k, 0)`) or deletion (`(0, k)`) after which the two lists agree
/// on a node.
fn pure_shift(ec: &[Node], ir: &[Node]) -> Option<(usize, usize)> {
    for k in 1..ec.len().max(ir.len()) {
        if k < ec.len() && strict_eq(&ec[k], &ir[0]) {
            return Some((k, 0));
        }
        if k < ir.len() && strict_eq(&ec[0], &ir[k]) {
            return Some((0, k));
        }
    }
    None
}

impl Aligner {
    fn mismatch(
        &mut self,
        kind: MismatchKind,
        path: &[PathStep],
        ec: Option<&Node>,
        ir: Option<&Node>,
    ) {
        self.out.mismatches.push(Mismatch {
            kind,
            path: path.to_vec(),
            ec: ec.map(|n| n.text.clone()),
            ec_pos: ec.and_then(|n| n.pos.clone()),
            ir: ir.map(describe_ir),
        });
    }

    fn record(&mut self, ec: &Node, ir: &Node, kind: DecisionKind) {
        self.out.matches.push(DecisionMatch {
            ir_label: ir.label.expect("an IR node carries its label"),
            kind,
            plumbing: ir.plumbing,
            ec: EcInstr {
                pos: ec.pos.clone(),
                pp: ec.text.clone(),
                lvalue: ec.lvalue.clone(),
            },
        });
    }

    fn lists(&mut self, ec: &[Node], ir: &[Node], path: &mut Vec<PathStep>) {
        let (mut i, mut j) = (0, 0);
        loop {
            // The IR end swallows what is left of EasyCrypt's block.
            if let Some(end) = ir.get(j).filter(|n| n.kind == NodeKind::End) {
                for n in ec[i..].iter().filter(|n| n.kind == NodeKind::Unknown) {
                    self.mismatch(MismatchKind::UnknownEcInstruction, path, Some(n), None);
                }
                self.out.matches.push(DecisionMatch {
                    ir_label: end.label.expect("an IR node carries its label"),
                    kind: DecisionKind::End,
                    plumbing: None,
                    ec: EcInstr {
                        pos: ec.get(i).and_then(|n| n.pos.clone()),
                        pp: ec.get(i).map_or(String::new(), |n| n.text.clone()),
                        lvalue: None,
                    },
                });
                return;
            }
            if let Some(n) = ec.get(i).filter(|n| n.kind == NodeKind::Unknown) {
                self.mismatch(MismatchKind::UnknownEcInstruction, path, Some(n), None);
                i += 1;
                continue;
            }
            match (ec.get(i), ir.get(j)) {
                (None, None) => return,
                (None, Some(_)) => {
                    for n in &ir[j..] {
                        self.mismatch(MismatchKind::MissingEcDecision, path, None, Some(n));
                    }
                    return;
                }
                (Some(_), None) => {
                    for n in &ec[i..] {
                        self.mismatch(MismatchKind::ExtraEcDecision, path, Some(n), None);
                    }
                    return;
                }
                (Some(e), Some(r)) if same_kind(e, r) => {
                    // A pair that is not an exact match may be off by an insertion or a
                    // deletion: prefer the shift that makes the rest line up.
                    if !strict_eq(e, r) {
                        if let Some((di, dj)) = pure_shift(&ec[i..], &ir[j..]) {
                            self.skip(&ec[i..i + di], &ir[j..j + dj], path);
                            i += di;
                            j += dj;
                            continue;
                        }
                    }
                    self.matched(e, r, path);
                    i += 1;
                    j += 1;
                }
                (Some(_), Some(_)) => {
                    let (di, dj) = self.resync_distance(&ec[i..], &ir[j..]);
                    self.skip(&ec[i..i + di], &ir[j..j + dj], path);
                    i += di;
                    j += dj;
                }
            }
        }
    }

    fn matched(&mut self, ec: &Node, ir: &Node, path: &mut Vec<PathStep>) {
        match (&ec.kind, &ir.kind) {
            (NodeKind::Branch { then: et, els: ee }, NodeKind::Branch { then: it, els: ie }) => {
                self.record(ec, ir, DecisionKind::Branch);
                let ir_label = ir.label.expect("an IR node carries its label");
                path.push(PathStep {
                    ir_label,
                    arm: Arm::Then,
                });
                self.lists(et, it, path);
                path.last_mut().expect("just pushed").arm = Arm::Else;
                self.lists(ee, ie, path);
                path.pop();
            }
            _ => self.record(ec, ir, DecisionKind::Sampling),
        }
    }

    /// How many nodes to skip on each side to reach the next pair that agrees completely
    /// (smallest total first). With no such pair, one node on each side is a substitution.
    fn resync_distance(&self, ec: &[Node], ir: &[Node]) -> (usize, usize) {
        for total in 1..(ec.len() + ir.len()) {
            for (di, e) in ec.iter().enumerate().take(total + 1) {
                let dj = total - di;
                if dj < ir.len() && strict_eq(e, &ir[dj]) {
                    return (di, dj);
                }
            }
        }
        (1, 1)
    }

    /// Reports the nodes a resynchronisation skips: pairs first as differing kinds, the rest as
    /// extra or missing.
    fn skip(&mut self, ec: &[Node], ir: &[Node], path: &[PathStep]) {
        let paired = ec.len().min(ir.len());
        for k in 0..paired {
            // An IR end (only ever last in its list) cannot be skipped over: it ends the walk.
            self.mismatch(MismatchKind::KindDiffers, path, Some(&ec[k]), Some(&ir[k]));
        }
        for n in &ec[paired..] {
            self.mismatch(MismatchKind::ExtraEcDecision, path, Some(n), None);
        }
        for n in &ir[paired..] {
            self.mismatch(MismatchKind::MissingEcDecision, path, None, Some(n));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::skeleton::Skeleton;

    fn branch(then: Skeleton, els: Skeleton) -> NodeKind {
        NodeKind::Branch { then, els }
    }
    fn ecb(text: &str, then: Skeleton, els: Skeleton) -> Node {
        Node::ec(branch(then, els), text)
    }
    fn ecs(text: &str) -> Node {
        Node::ec(NodeKind::Sampling, text)
    }
    fn irb(label: Label, then: Skeleton, els: Skeleton) -> Node {
        Node::ir(branch(then, els), label, None)
    }
    fn irs(label: Label) -> Node {
        Node::ir(NodeKind::Sampling, label, None)
    }
    fn end(label: Label) -> Node {
        Node::ir(NodeKind::End, label, None)
    }
    fn kinds(a: &Alignment) -> Vec<MismatchKind> {
        a.mismatches.iter().map(|m| m.kind).collect()
    }

    #[test]
    fn equal_skeletons_match_and_the_branches_recurse() {
        let ec = [ecb("c", vec![ecs("x <$ d")], vec![]), ecs("y <$ d")];
        let ir = [irb(1, vec![irs(2)], vec![]), irs(3)];
        let a = align(&ec, &ir);
        assert!(a.is_aligned(), "{a:?}");
        let labels: Vec<Label> = a.matches.iter().map(|m| m.ir_label).collect();
        assert_eq!(labels, [1, 2, 3]);
        assert_eq!(a.ec_for(2).unwrap().pp, "x <$ d");
    }

    #[test]
    fn an_ir_end_matches_the_rest_of_the_easycrypt_block() {
        // the router tail `if (ec_result = None) { … }` follows what the IR ends with
        let ec = [ecs("x <$ d"), ecb("ec_result = None", vec![], vec![])];
        let ir = [irs(1), end(2)];
        let a = align(&ec, &ir);
        assert!(a.is_aligned(), "{a:?}");
        assert_eq!(a.ec_for(2).unwrap().pp, "ec_result = None");
    }

    #[test]
    fn an_end_inside_a_branch_leaves_the_siblings_after_the_branch_to_align() {
        let ec = [
            ecb("c", vec![], vec![]),
            ecb("guard", vec![ecs("x <$ d")], vec![]),
        ];
        let ir = [irb(1, vec![end(2)], vec![]), irb(3, vec![irs(4)], vec![])];
        assert!(align(&ec, &ir).is_aligned());
    }

    #[test]
    fn kind_differs() {
        let a = align(&[ecs("x <$ d")], &[irb(1, vec![], vec![])]);
        assert_eq!(kinds(&a), [MismatchKind::KindDiffers]);
        assert_eq!(a.mismatches[0].ec.as_deref(), Some("x <$ d"));
        assert!(a.mismatches[0].ir.as_deref().unwrap().contains("@L1"));
    }

    #[test]
    fn extra_ec_decision_at_the_end() {
        let a = align(&[ecs("x <$ d"), ecs("y <$ d")], &[irs(1)]);
        assert_eq!(kinds(&a), [MismatchKind::ExtraEcDecision]);
        assert_eq!(a.mismatches[0].ec.as_deref(), Some("y <$ d"));
    }

    #[test]
    fn missing_ec_decision_at_the_end() {
        let a = align(&[ecs("x <$ d")], &[irs(1), irs(2)]);
        assert_eq!(kinds(&a), [MismatchKind::MissingEcDecision]);
    }

    #[test]
    fn unknown_ec_instruction_is_reported_and_skipped() {
        let ec = [Node::ec(NodeKind::Unknown, "while (i < 3) { … }"), ecs("x <$ d")];
        let a = align(&ec, &[irs(1)]);
        assert_eq!(kinds(&a), [MismatchKind::UnknownEcInstruction]);
        assert_eq!(a.matches.len(), 1);
    }

    #[test]
    fn a_mismatch_resynchronises_on_the_next_agreeing_pair() {
        // an extra `if` in EasyCrypt, then everything else agrees, including a nested mismatch
        let ec = [
            ecb("surprise", vec![], vec![]),
            ecb("c", vec![ecs("a <$ d")], vec![]),
            ecs("b <$ d"),
        ];
        let ir = [irb(1, vec![irs(2)], vec![]), irs(3)];
        let a = align(&ec, &ir);
        assert_eq!(kinds(&a), [MismatchKind::ExtraEcDecision]);
        assert_eq!(a.mismatches[0].ec.as_deref(), Some("surprise"));
        let labels: Vec<Label> = a.matches.iter().map(|m| m.ir_label).collect();
        assert_eq!(labels, [1, 2, 3], "everything after the surprise still aligns");
    }

    #[test]
    fn a_mismatch_inside_a_branch_carries_its_path_and_does_not_hide_later_ones() {
        let ec = [ecb("c", vec![ecs("a <$ d")], vec![ecs("z <$ d")]), ecs("b <$ d")];
        let ir = [irb(7, vec![irs(8), irs(9)], vec![]), irs(10)];
        let a = align(&ec, &ir);
        assert_eq!(
            kinds(&a),
            [MismatchKind::MissingEcDecision, MismatchKind::ExtraEcDecision]
        );
        assert_eq!(
            a.mismatches[0].path,
            [PathStep {
                ir_label: 7,
                arm: Arm::Then
            }]
        );
        assert_eq!(
            a.mismatches[1].path,
            [PathStep {
                ir_label: 7,
                arm: Arm::Else
            }]
        );
        assert!(a.matches.iter().any(|m| m.ir_label == 10));
    }

    #[test]
    fn the_router_guard_is_peeled_and_its_absence_is_a_router_shape_mismatch() {
        let flag = "Comp_X.Game_X.abort_flag";
        let guard = ecb(&format!("!{flag}"), vec![ecs("x <$ d")], vec![]);
        let a = align_router(std::slice::from_ref(&guard), &[irs(1), end(2)], flag);
        assert!(a.is_aligned(), "{a:?}");

        let a = align_router(&[ecs("x <$ d")], &[irs(1)], flag);
        assert_eq!(kinds(&a), [MismatchKind::RouterShape]);

        let a = align_router(&[guard.clone(), ecs("y <$ d")], &[irs(1)], flag);
        assert_eq!(kinds(&a), [MismatchKind::RouterShape]);

        let other = ecb("!Other.abort_flag", vec![], vec![]);
        let a = align_router(&[other], &[], flag);
        assert_eq!(kinds(&a), [MismatchKind::RouterShape]);
    }
}
