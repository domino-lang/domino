// SPDX-License-Identifier: MIT OR Apache-2.0

//! Decision skeletons (`CONTEXT.md`, ADR 0002): a program with its straight-line code erased,
//! leaving its branches, samplings and ends.
//!
//! Two sources produce one type. [`ec_skeleton`] walks the instruction list of a goal's program
//! as `easycrypt cli -json` shows it; [`ir_skeleton`] walks an [`InlinedOracle`], the lowering
//! the lockstep execution runs on. [`super::align`] ties the two together.

use crate::debug::ir::{InlBlock, InlStmt, InlinedOracle, Label, Plumbing};

use super::json::Instr;

/// Which side of a branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arm {
    Then,
    Else,
}

/// Where an instruction sits in EasyCrypt's program: the branches leading to its block, each as
/// (index of the `if` in its block's statement list, arm), then its index in the final block's
/// statement list. Indices count **every** statement, assignments included, exactly as
/// EasyCrypt does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcPos {
    pub path: Vec<(usize, Arm)>,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeKind {
    /// A conditional, with the skeletons of both blocks (`els` is empty when there is no else).
    Branch { then: Skeleton, els: Skeleton },
    Sampling,
    /// An IR terminal. EasyCrypt's own end is implicit: the end of the program.
    End,
    /// An EasyCrypt instruction the skeleton cannot classify (`while`, `match`, a remaining
    /// `call`, …).
    Unknown,
}

/// A skeleton: a sequence of decision nodes.
pub type Skeleton = Vec<Node>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    /// EasyCrypt side: the condition's or the instruction's `pp`. IR side: the listing line.
    pub text: String,
    /// A sampling's target as EasyCrypt prints it (story 27 needs the name).
    pub lvalue: Option<String>,
    /// IR side: the listing label of the decision.
    pub label: Option<Label>,
    /// IR side: why a branch exists when it decides nothing Domino would call a decision.
    pub plumbing: Option<Plumbing>,
    /// EasyCrypt side: where the instruction is.
    pub pos: Option<EcPos>,
}

impl Node {
    fn new(kind: NodeKind, text: String) -> Node {
        Node {
            kind,
            text,
            lvalue: None,
            label: None,
            plumbing: None,
            pos: None,
        }
    }

    /// A hand-built EasyCrypt-side node, for tests and callers that build skeletons directly.
    pub fn ec(kind: NodeKind, text: &str) -> Node {
        Node::new(kind, text.to_string())
    }

    /// A hand-built IR-side node.
    pub fn ir(kind: NodeKind, label: Label, plumbing: Option<Plumbing>) -> Node {
        Node {
            label: Some(label),
            plumbing,
            ..Node::new(kind, String::new())
        }
    }
}

/// The skeleton of an EasyCrypt instruction list. Assignments are skipped; `if` is a branch,
/// `rnd` a sampling, anything else unknown.
pub fn ec_skeleton(stmts: &[Instr]) -> Skeleton {
    ec_skeleton_at(stmts, &[])
}

fn ec_skeleton_at(stmts: &[Instr], path: &[(usize, Arm)]) -> Skeleton {
    let mut out = Vec::new();
    for (index, stmt) in stmts.iter().enumerate() {
        let pos = EcPos {
            path: path.to_vec(),
            index,
        };
        let node = match stmt.kind.as_str() {
            "asgn" => continue,
            "if" => {
                let arm = |a: Arm, block: &[Instr]| {
                    let mut p = path.to_vec();
                    p.push((index, a));
                    ec_skeleton_at(block, &p)
                };
                Node {
                    pos: Some(pos),
                    ..Node::new(
                        NodeKind::Branch {
                            then: arm(Arm::Then, &stmt.then_block),
                            els: arm(Arm::Else, &stmt.else_block),
                        },
                        stmt.cond.as_ref().map_or_else(String::new, |c| c.pp.clone()),
                    )
                }
            }
            "rnd" => Node {
                lvalue: stmt.lvalue.as_ref().map(|l| l.pp.clone()),
                pos: Some(pos),
                ..Node::new(NodeKind::Sampling, stmt.pp.clone())
            },
            _ => Node {
                pos: Some(pos),
                ..Node::new(NodeKind::Unknown, stmt.pp.clone())
            },
        };
        out.push(node);
    }
    out
}

/// The skeleton of an inlined oracle. An inlined call is transparent, as after `proc; inline.`
/// EasyCrypt has inlined it too: its nodes are spliced into the caller's sequence, and its
/// `Return` and fall-through `Abort` (which in EasyCrypt are assignments to its result) leave
/// nothing. A terminal of the entry frame is an [`NodeKind::End`].
pub fn ir_skeleton(oracle: &InlinedOracle) -> Skeleton {
    let mut out = Vec::new();
    ir_block(&oracle.body, false, oracle, &mut out);
    out
}

fn ir_block(block: &InlBlock, in_callee: bool, oracle: &InlinedOracle, out: &mut Skeleton) {
    let line = |label: Label| {
        oracle
            .listing
            .sites
            .get(&label)
            .map(|site| site.line.clone())
            .unwrap_or_default()
    };
    for stmt in &block.0 {
        match stmt {
            InlStmt::Assign { .. } => {}
            InlStmt::Sample { label, .. } => out.push(Node {
                label: Some(*label),
                ..Node::new(NodeKind::Sampling, line(*label))
            }),
            InlStmt::Unwrap { label, .. } => {
                let end = Node::ir(NodeKind::End, *label, None);
                out.push(Node {
                    label: Some(*label),
                    ..Node::new(
                        NodeKind::Branch {
                            then: vec![],
                            els: vec![end],
                        },
                        line(*label),
                    )
                });
            }
            InlStmt::Branch {
                label,
                then,
                els,
                plumbing,
                ..
            } => {
                let mut t = Vec::new();
                ir_block(then, in_callee, oracle, &mut t);
                let mut e = Vec::new();
                ir_block(els, in_callee, oracle, &mut e);
                out.push(Node {
                    label: Some(*label),
                    plumbing: *plumbing,
                    ..Node::new(NodeKind::Branch { then: t, els: e }, line(*label))
                });
            }
            InlStmt::Call { body, .. } => ir_block(body, true, oracle, out),
            InlStmt::Return { label, .. } | InlStmt::Abort { label } => {
                if !in_callee {
                    out.push(Node {
                        label: Some(*label),
                        ..Node::new(NodeKind::End, line(*label))
                    });
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::easycrypt::json::parse_response;

    /// A goal after `proc; inline.` on hello-world's `UsefulOracle` (story 25's binary, r2026.09):
    /// left is the router with the callee inlined, right the same without the extra call.
    const FIXTURE: &str =
        include_str!("../../testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json");

    #[test]
    fn skeleton_of_the_json_program_keeps_decisions_and_drops_assignments() {
        let response = parse_response(FIXTURE).unwrap();
        let goal = &response.proof.as_ref().unwrap().goals[0];
        assert_eq!(goal.concl.kind, "equivS");
        let left = ec_skeleton(&goal.concl.left.as_ref().unwrap().stmt);
        assert_eq!(left.len(), 1, "only the router's guard at top level: {left:#?}");
        assert!(left[0].text.contains("abort_flag"));
        let NodeKind::Branch { then, els } = &left[0].kind else {
            panic!("the router guard is a branch")
        };
        assert!(els.is_empty());
        // inside: the sampling, the call-result `if`, the abort-flag tail
        let kinds: Vec<&str> = then
            .iter()
            .map(|n| match n.kind {
                NodeKind::Sampling => "rnd",
                NodeKind::Branch { .. } => "if",
                _ => "other",
            })
            .collect();
        assert_eq!(kinds, ["rnd", "if", "if"]);
        assert_eq!(then[0].lvalue.as_deref(), Some("rand"));
        // positions count every statement: `rnd` is the 5th statement of the guard's block
        let pos = then[0].pos.as_ref().unwrap();
        assert_eq!(pos.path, vec![(1, Arm::Then)]);
        assert_eq!(pos.index, 3);
    }
}
