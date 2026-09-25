// SPDX-License-Identifier: MIT OR Apache-2.0

//! Lockstep execution (`docs/stories/easycrypt/23-lockstep-execution.md`).
//!
//! The sequential debugger walks every left path and, under each, every right
//! path. An EasyCrypt pRHL proof instead advances both programs together and
//! decides each branch jointly. [`run_lockstep`] does the same: it owns one
//! executor per side and walks the **joint tree** depth first.
//!
//! # A joint node
//!
//! Each side consumes its straight-line code (assignments, call entry and exit,
//! callee returns) up to its next *decision point*: a branch, a sampling, or
//! the end of the oracle. The two decision points are then resolved by the
//! first rule that fits, with `A` the assumptions on the solver stack and `pc`
//! both sides' path conditions:
//!
//! 1. **Determined branch** ([`NodeKind::Determined`]): a side's condition `c`
//!    has `A ∧ pc ∧ ¬c` or `A ∧ pc ∧ c` unsatisfiable. That side takes the
//!    determined child alone, left before right. If both are unsatisfiable the
//!    node is unreachable ([`NodeKind::Unreachable`]). A plumbing `DoneGuard`
//!    (condition `true`) always resolves here.
//! 2. **Synchronized branch**: both sides at undetermined branches and
//!    `A ∧ pc ∧ (c_L ≠ c_R)` unsatisfiable: (then, then) and (else, else).
//! 3. **Split**: any other branch situation; every combination of the
//!    outcomes, the unsatisfiable ones pruned. Branches go before samplings.
//! 4. **Samplings**, when neither side is at a branch. Both at samplings with
//!    `A ∧ pc ∧ draw_L ≠ draw_R` unsatisfiable: consume both. Otherwise a side's
//!    head sampling is *independent* when, for every candidate the randomness
//!    mapping could pair it with, the mapping's premise is unsatisfiable under
//!    `A ∧ pc`: consume it alone, left first. Otherwise it is a **stuck point**
//!    ([`StuckPoint`]): recorded, consumed with Domino's semantics (the draw is
//!    still the game's `rand` term, so the mapping keeps constraining it), and
//!    execution goes on. The mapping's text is never read; it may depend on
//!    the state and the arguments.
//! 5. **Terminal pair**: both sides at terminals. After an unconditional
//!    vacuity check, *equal-output* and *invariant* are checked, and, when the
//!    invariant is not verified, each state relation on its own.
//!
//! Only `unsat` prunes; `unknown` is always explored, exactly as in the
//! sequential debugger.
//!
//! # Driving it
//!
//! [`run_lockstep`] reports to a [`LockstepObserver`] in depth-first order, so
//! a consumer (the viewer, the tactic generator of story 27) can act on each
//! node with the solver stack at that node's state. The engine also returns the
//! whole [`LockstepOutcome`]. The tree is an arena, [`JointTree::nodes`], in
//! depth-first pre-order; a node's children point into it.
//!
//! # Identifiers
//!
//! `J<n>` numbers joint paths and `S<n>` stuck points, from 1, in depth-first
//! order (then before else, left before right). They depend on nothing but the
//! project, so an unchanged project gives identical ids.
//!
//! The engine is listing-agnostic: it takes two [`InlinedOracle`]s together
//! with the game instances and sample infos they execute against.

use std::ops::ControlFlow;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use serde_derive::Serialize;

use crate::debug::claims::{check_claim, ClaimQuery, PairAborts};
use crate::debug::driver::{
    lines_view, steps_view, terminal_view, write_model, ClaimVerdict, DebugError, StepView,
    StopReason, TerminalView, Verdict,
};
use crate::debug::layout::Layout;
use crate::debug::effect::PathEffect;
use crate::debug::exec::{
    BranchForm, BranchHead, Decision, Head, SampleHead, Side, SideExec, SidePos, Terminal,
    TerminalPath,
};
use crate::debug::ir::{InlinedOracle, Plumbing};
use crate::theorem::GameInstance;
use crate::transforms::samplify::SampleInfo;
use crate::util::smtsolver::{SmtSolver, SmtSolverResponse};
use crate::writers::smt::exprs::{SmtAssert, SmtEq2, SmtExpr, SmtNot, SmtOr};

// ---------------------------------------------------------------------------
// Inputs
// ---------------------------------------------------------------------------

/// One side of a lockstep execution.
pub struct LockstepSide<'a> {
    pub inlined: &'a InlinedOracle,
    /// The game instance `inlined` executes against: the Domino one
    /// (`DebugTransform`), whose state places, sample ids and entry returns the
    /// claims are built from.
    pub game_inst: &'a GameInstance,
    pub sample_info: &'a SampleInfo,
}

/// The solver-side vocabulary of the check, built once from the equivalence.
/// The assumptions `A` themselves are not here: they are on the solver stack
/// when [`run_lockstep`] is called.
pub struct LockstepTerms {
    /// The claims checked on every joint path, in order. Each keeps its own declared
    /// dependencies (asserted at the terminal pair, one `push` above the paths); the claim set
    /// of the EasyCrypt listing has none, and groups `equal-aborts` and `same-output` as
    /// `equal-output`.
    pub claims: Vec<ClaimQuery>,
    /// One entry per state relation the invariant conjoins, in file order.
    pub relations: Vec<RelationGoal>,
    /// Every pairing the randomness mapping could make.
    pub pairings: Vec<Pairing>,
}

/// One state relation's negated goal on the new states.
pub struct RelationGoal {
    pub name: String,
    pub negated: SmtExpr,
}

/// A candidate pairing of the randomness mapping: the left sampling
/// `left_sample` at its `offset_left`-th draw with the right sampling
/// `right_sample` at its `offset_right`-th draw. `premise` is the mapping's
/// condition for it, over the global constants (so it may depend on the state
/// and the arguments). Samples are indices into the sides' `SampleInfo`.
pub struct Pairing {
    pub left_sample: usize,
    pub right_sample: usize,
    pub offset_left: usize,
    pub offset_right: usize,
    pub premise: SmtExpr,
}

pub struct LockstepOptions<'a> {
    /// Stop after this many joint paths.
    pub max_paths: Option<usize>,
    /// `Ctrl-C`: checked at every node.
    pub stop: Option<&'a AtomicBool>,
    /// Where models of failing checks go: `<out_dir>/models/<J>.<check>.smt2`, with the
    /// layout's prefix for a Domino listing.
    pub out_dir: &'a Path,
    pub layout: Layout,
}

/// Called in depth-first order while [`run_lockstep`] runs. Every method has a
/// no-op default. `outcome` is what has been found so far; the solver stack
/// holds the state of the node being reported.
pub trait LockstepObserver {
    /// Node `node` has been decided; its children are not explored yet.
    fn node_entered(&mut self, _outcome: &LockstepOutcome, _node: usize) -> Result<(), DebugError> {
        Ok(())
    }
    /// The engine is about to explore child number `child` of `node`.
    fn child_entered(
        &mut self,
        _outcome: &LockstepOutcome,
        _node: usize,
        _child: usize,
    ) -> Result<(), DebugError> {
        Ok(())
    }
    /// A joint path ended: `node` is its terminal-pair node. `left` and `right`
    /// are the two sides' finished paths, with their SMT.
    fn pair_checked(
        &mut self,
        _outcome: &LockstepOutcome,
        _pair: &PairRecord,
        _left: &TerminalPath,
        _right: &TerminalPath,
        _elapsed: Duration,
    ) -> Result<(), DebugError> {
        Ok(())
    }
    /// The node has a stuck point.
    fn stuck_found(&mut self, _outcome: &LockstepOutcome, _stuck: &StuckPoint) {}
    /// Every child of `node` has been explored or pruned.
    fn node_left(&mut self, _outcome: &LockstepOutcome, _node: usize) {}
}

// ---------------------------------------------------------------------------
// Outputs (serialised into trace.json, schema 9)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct LockstepOutcome {
    pub tree: JointTree,
    /// The joint paths, `J1`, `J2`, … in depth-first order.
    pub pairs: Vec<PairRecord>,
    /// The stuck points, `S1`, `S2`, … in depth-first order.
    pub stuck: Vec<StuckPoint>,
    pub stop_reason: StopReason,
}

/// The joint tree as an arena in depth-first pre-order; node 0 is the root.
#[derive(Debug, Clone, Default, Serialize)]
pub struct JointTree {
    pub nodes: Vec<JointNode>,
}

#[derive(Debug, Clone, Serialize)]
pub struct JointNode {
    pub index: usize,
    pub kind: NodeKind,
    /// Where each side stood when the node was decided.
    pub left: SideView,
    pub right: SideView,
    /// Every solver query the decision took, in order.
    pub answers: Vec<SolverAnswer>,
    pub children: Vec<JointChild>,
    /// `J<n>`, for a terminal pair.
    pub pair: Option<String>,
    /// `S<n>`, for a stuck point.
    pub stuck: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NodeKind {
    /// A side's branch was decided by the assumptions and the path condition;
    /// that side went alone.
    Determined,
    /// Both sides at branches with equivalent conditions.
    Synchronized,
    /// Any other branch situation: every combination, the infeasible pruned.
    Split,
    /// Both sides at samplings the mapping forces to draw equal values.
    SamplingSynchronized,
    /// A sampling the mapping relates to nothing; consumed on its side alone.
    SamplingIndependent,
    /// A sampling EasyCrypt could not be handed a step for; see [`StuckPoint`].
    Stuck,
    /// Both sides at their ends: the checks ran.
    TerminalPair,
    /// The assumptions and both path conditions are contradictory (the node is
    /// unreachable). Not one of the story's kinds: it is the "prune it" of the
    /// determined-branch rule, made visible.
    Unreachable,
}

impl NodeKind {
    pub fn as_str(self) -> &'static str {
        match self {
            NodeKind::Determined => "determined",
            NodeKind::Synchronized => "synchronized",
            NodeKind::Split => "split",
            NodeKind::SamplingSynchronized => "sampling-synchronized",
            NodeKind::SamplingIndependent => "sampling-independent",
            NodeKind::Stuck => "stuck",
            NodeKind::TerminalPair => "terminal-pair",
            NodeKind::Unreachable => "unreachable",
        }
    }
}

/// Where one side stood at a node.
#[derive(Debug, Clone, Serialize)]
pub struct SideView {
    pub head: HeadView,
    /// The listing lines this side consumed on the way here, since the last
    /// decision it took, as inclusive ranges. For the viewer only: story 27 does
    /// not use them as EasyCrypt positions (ADR 0002).
    pub consumed: Vec<[usize; 2]>,
    /// Set when the branch the side stands at is plumbing (`CONTEXT.md`).
    pub plumbing: Option<PlumbingKind>,
}

#[derive(Debug, Clone, Serialize)]
pub struct HeadView {
    pub kind: HeadKind,
    /// The label of the decision point in the side's listing.
    pub label: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HeadKind {
    Branch,
    Unwrap,
    Sample,
    Return,
    Abort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PlumbingKind {
    DoneGuard,
    CallResult,
}

impl From<Plumbing> for PlumbingKind {
    fn from(p: Plumbing) -> Self {
        match p {
            Plumbing::DoneGuard => PlumbingKind::DoneGuard,
            Plumbing::CallResult => PlumbingKind::CallResult,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct JointChild {
    /// What the left side did to get into the child; `None` if it waited.
    pub left: Option<SideStep>,
    pub right: Option<SideStep>,
    pub outcome: ChildOutcome,
}

#[derive(Debug, Clone, Serialize)]
pub struct SideStep {
    pub label: usize,
    /// A branch decision (`then`, `else`, `assert-holds`, …) or `draw` for a
    /// sampling.
    pub decision: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ChildOutcome {
    /// Explored: the node's index in [`JointTree::nodes`].
    Explored { node: usize },
    /// The solver proved the combination infeasible.
    Pruned { answer: SolverAnswer },
    /// The run stopped before reaching it.
    NotExplored,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

impl From<SmtSolverResponse> for Answer {
    fn from(r: SmtSolverResponse) -> Self {
        match r {
            SmtSolverResponse::Sat => Answer::Sat,
            SmtSolverResponse::Unsat => Answer::Unsat,
            SmtSolverResponse::Unknown => Answer::Unknown,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct SolverAnswer {
    /// What was asked, e.g. `left-then-possible`: satisfiability of
    /// `A ∧ pc ∧ <the named condition>`.
    pub query: String,
    pub answer: Answer,
}

#[derive(Debug, Clone, Serialize)]
pub struct StuckPoint {
    pub id: String,
    /// The node the point sits at.
    pub node: usize,
    /// `left` or `right`: the side whose sampling is stuck.
    pub side: &'static str,
    /// The stuck sampling's label in its side's listing.
    pub label: usize,
    /// Both sides' decision-point labels at the point.
    pub left_label: usize,
    pub right_label: usize,
    /// `<instance>.<oracle>.<name>` of the sampling and how many times it had
    /// been drawn before.
    pub sample: String,
    pub draw: usize,
    pub reason: StuckReason,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum StuckReason {
    /// The mapping pairs the sampling with another one for certain, but that
    /// one is not at the other side's head.
    PartnerNotAtHead,
    /// The pairing holds under some executions only, so a proof cannot pair it.
    PairingSatNotValid,
    /// The solver could not decide the pairing.
    PairingUnknown,
    /// The mapping pairs the sampling for certain, but the other side has
    /// already ended.
    NoPartnerReachable,
}

impl StuckReason {
    pub fn as_str(self) -> &'static str {
        match self {
            StuckReason::PartnerNotAtHead => "partner-not-at-head",
            StuckReason::PairingSatNotValid => "pairing-sat-not-valid",
            StuckReason::PairingUnknown => "pairing-unknown",
            StuckReason::NoPartnerReachable => "no-partner-reachable",
        }
    }
}

/// One joint path and what the checks said about it.
#[derive(Debug, Clone, Serialize)]
pub struct PairRecord {
    /// `J<n>`.
    pub id: String,
    /// Its terminal-pair node.
    pub node: usize,
    pub left: PairSide,
    pub right: PairSide,
    /// What each claim said about the pair, in the order the run checks them. On the
    /// EasyCrypt listing: `equal-output` and `invariant`.
    pub claims: Vec<ClaimVerdict>,
}

/// The name under which the EasyCrypt listing groups `equal-aborts` and `same-output`: with the
/// empty dependency set they genuinely share, the pair reads as one claim.
pub const EQUAL_OUTPUT: &str = "equal-output";

impl PairRecord {
    /// What the claim called `claim` said about this pair.
    pub fn verdict_of(&self, claim: &str) -> Option<&Verdict> {
        self.claims
            .iter()
            .find(|c| c.claim == claim)
            .map(|c| &c.verdict)
    }

    /// Per-relation verdicts of the `invariant` claim, present only when it is neither
    /// `verified` nor `unreachable`.
    pub fn relations(&self) -> &[RelationVerdict] {
        self.claims
            .iter()
            .find(|c| c.claim == "invariant")
            .map_or(&[], |c| c.relations.as_slice())
    }

    /// Some claim failed or could not be decided.
    pub fn has_failure(&self) -> bool {
        self.claims.iter().any(|c| {
            c.verdict.is_failure() || c.relations.iter().any(|r| r.verdict.is_failure())
        })
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct PairSide {
    pub steps: Vec<StepView>,
    pub terminal: TerminalView,
    /// Listing lines this side executed on the path, as inclusive ranges.
    pub lines: Vec<[usize; 2]>,
    /// What the side computed; `None` for an abort.
    pub effect: Option<PathEffect>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RelationVerdict {
    pub name: String,
    pub verdict: Verdict,
}

// ---------------------------------------------------------------------------
// The engine
// ---------------------------------------------------------------------------

/// One side's place in the joint execution: where it stands and the decision
/// point it waits at.
#[derive(Clone)]
struct SideState<'a> {
    pos: SidePos<'a>,
    head: Head<'a>,
}

#[derive(Clone)]
struct Joint<'a> {
    left: SideState<'a>,
    right: SideState<'a>,
}

impl<'a> Joint<'a> {
    fn side(&self, side: Side) -> &SideState<'a> {
        match side {
            Side::Left => &self.left,
            Side::Right => &self.right,
        }
    }
}

/// What a node decided: its kind and its children, each already in the state
/// it starts from.
struct Plan<'a> {
    kind: NodeKind,
    children: Vec<PlannedChild<'a>>,
    stuck: Option<StuckDraft>,
}

struct PlannedChild<'a> {
    left: Option<SideStep>,
    right: Option<SideStep>,
    joint: Joint<'a>,
    /// Ask the solver whether the combination is feasible before exploring.
    check_feasible: bool,
}

struct StuckDraft {
    side: Side,
    label: usize,
    sample: String,
    draw: usize,
    reason: StuckReason,
}

#[allow(clippy::large_enum_variant)] // one short-lived value per node
enum Decided<'a> {
    Plan {
        plan: Plan<'a>,
        pair: Option<(PairRecord, TerminalPath, TerminalPath, Duration)>,
    },
    /// The run stops here (`--max-paths`).
    Stop,
}

enum Classification {
    Independent,
    Stuck(StuckReason),
}

struct Engine<'r, 'a, S: SmtSolver> {
    solver: &'r mut S,
    terms: &'r LockstepTerms,
    opts: &'r LockstepOptions<'r>,
    observer: &'r mut dyn LockstepObserver,
    left: SideExec<'a>,
    right: SideExec<'a>,
    left_inlined: &'a InlinedOracle,
    right_inlined: &'a InlinedOracle,
    out: LockstepOutcome,
}

/// Run lockstep execution of `left` against `right`.
///
/// `solver` must already hold the assumptions `A` at level 0 (the base frame:
/// declarations, game definitions, invariants on the old states, the
/// randomness-mapping condition, the shared arguments). It is returned to that
/// state, whatever the outcome.
pub fn run_lockstep<S: SmtSolver>(
    solver: &mut S,
    left: LockstepSide<'_>,
    right: LockstepSide<'_>,
    terms: &LockstepTerms,
    opts: &LockstepOptions<'_>,
    observer: &mut dyn LockstepObserver,
) -> Result<LockstepOutcome, DebugError> {
    let mut left_exec = SideExec::new(left.inlined, left.game_inst, left.sample_info, Side::Left)?;
    let mut right_exec = SideExec::new(
        right.inlined,
        right.game_inst,
        right.sample_info,
        Side::Right,
    )?;
    let (left_pos, left_head) = left_exec.start();
    let (right_pos, right_head) = right_exec.start();
    let root = Joint {
        left: SideState {
            pos: left_pos,
            head: left_head,
        },
        right: SideState {
            pos: right_pos,
            head: right_head,
        },
    };

    let mut engine = Engine {
        solver,
        terms,
        opts,
        observer,
        left: left_exec,
        right: right_exec,
        left_inlined: left.inlined,
        right_inlined: right.inlined,
        out: LockstepOutcome {
            tree: JointTree::default(),
            pairs: Vec::new(),
            stuck: Vec::new(),
            stop_reason: StopReason::Completed,
        },
    };
    let _ = engine.explore(root)?;
    Ok(engine.out)
}

impl<'a, S: SmtSolver> Engine<'_, 'a, S> {
    fn exec(&mut self, side: Side) -> &mut SideExec<'a> {
        match side {
            Side::Left => &mut self.left,
            Side::Right => &mut self.right,
        }
    }

    fn stopped(&mut self) -> bool {
        if self.opts.stop.is_some_and(|s| s.load(Ordering::Relaxed)) {
            self.out.stop_reason = StopReason::Interrupted;
            return true;
        }
        false
    }

    /// Explore the joint node `joint` in a solver scope of its own.
    fn explore(&mut self, joint: Joint<'a>) -> Result<ControlFlow<()>, DebugError> {
        if self.stopped() {
            return Ok(ControlFlow::Break(()));
        }
        self.solver.push()?;
        let result = self.explore_scoped(joint);
        let popped = self.solver.pop();
        let flow = result?;
        popped?;
        Ok(flow)
    }

    fn explore_scoped(&mut self, mut joint: Joint<'a>) -> Result<ControlFlow<()>, DebugError> {
        self.assert_pending(&mut joint)?;

        let (decided, (left_view, right_view, answers)) = self.decide(&mut joint)?;
        let Decided::Plan { plan, pair } = decided else {
            return Ok(ControlFlow::Break(()));
        };

        // Record the node.
        let index = self.out.tree.nodes.len();
        let stuck_id = plan
            .stuck
            .as_ref()
            .map(|_| format!("S{}", self.out.stuck.len() + 1));
        let pair_id = pair
            .as_ref()
            .map(|_| format!("J{}", self.out.pairs.len() + 1));
        self.out.tree.nodes.push(JointNode {
            index,
            kind: plan.kind,
            left: left_view,
            right: right_view,
            answers,
            children: plan
                .children
                .iter()
                .map(|c| JointChild {
                    left: c.left.clone(),
                    right: c.right.clone(),
                    outcome: ChildOutcome::NotExplored,
                })
                .collect(),
            pair: pair_id.clone(),
            stuck: stuck_id.clone(),
        });

        let stuck = plan.stuck.as_ref().map(|draft| StuckPoint {
            id: stuck_id.expect("a stuck plan got an id"),
            node: index,
            side: side_name(draft.side),
            label: draft.label,
            left_label: head_label(&joint.left.head),
            right_label: head_label(&joint.right.head),
            sample: draft.sample.clone(),
            draw: draft.draw,
            reason: draft.reason,
        });
        if let Some(stuck) = &stuck {
            self.out.stuck.push(stuck.clone());
        }
        let pair = pair.map(|(mut record, left_path, right_path, elapsed)| {
            record.id = pair_id.expect("a pair got an id");
            record.node = index;
            self.out.pairs.push(record.clone());
            (record, left_path, right_path, elapsed)
        });

        // the node, then what was found at it
        self.observer.node_entered(&self.out, index)?;
        if let Some(stuck) = &stuck {
            self.observer.stuck_found(&self.out, stuck);
        }
        if let Some((record, left_path, right_path, elapsed)) = &pair {
            self.observer
                .pair_checked(&self.out, record, left_path, right_path, *elapsed)?;
        }

        // Explore the children.
        let mut flow = ControlFlow::Continue(());
        for (i, child) in plan.children.into_iter().enumerate() {
            if let Some(answer) = self.infeasible(&child)? {
                self.out.tree.nodes[index].children[i].outcome = ChildOutcome::Pruned { answer };
                continue;
            }
            let child_node = self.out.tree.nodes.len();
            self.out.tree.nodes[index].children[i].outcome =
                ChildOutcome::Explored { node: child_node };
            self.observer.child_entered(&self.out, index, i)?;
            let child_flow = self.explore(child.joint)?;
            if self.out.tree.nodes.len() == child_node {
                // The run stopped before the child recorded anything.
                self.out.tree.nodes[index].children[i].outcome = ChildOutcome::NotExplored;
            }
            if child_flow.is_break() {
                flow = ControlFlow::Break(());
                break;
            }
        }
        self.observer.node_left(&self.out, index);
        Ok(flow)
    }

    /// Put everything either side produced since the last flush on the solver
    /// stack.
    fn assert_pending(&mut self, joint: &mut Joint<'a>) -> Result<(), DebugError> {
        for side in [&mut joint.left, &mut joint.right] {
            let (decls, constraints) = side.pos.pending();
            for e in decls.iter().chain(constraints) {
                self.solver.write_smt(e.clone())?;
            }
            side.pos.mark_reported();
        }
        Ok(())
    }

    /// Is `A ∧ pc ∧ <the child's outcome>` unsatisfiable? Only `unsat` prunes.
    fn infeasible(&mut self, child: &PlannedChild<'a>) -> Result<Option<SolverAnswer>, DebugError> {
        if !child.check_feasible {
            return Ok(None);
        }
        self.solver.push()?;
        let mut asked = || -> Result<SmtSolverResponse, DebugError> {
            for side in [&child.joint.left, &child.joint.right] {
                let (decls, constraints) = side.pos.pending();
                for e in decls.iter().chain(constraints) {
                    self.solver.write_smt(e.clone())?;
                }
            }
            Ok(self.solver.check_sat()?)
        };
        let answer = asked();
        self.solver.pop()?;
        Ok(match answer? {
            SmtSolverResponse::Unsat => Some(SolverAnswer {
                query: "combination-feasible".to_string(),
                answer: Answer::Unsat,
            }),
            _ => None,
        })
    }

    /// Ask whether `A ∧ pc ∧ extra…` is satisfiable, and record the answer.
    fn ask(
        &mut self,
        answers: &mut Vec<SolverAnswer>,
        query: impl Into<String>,
        extra: Vec<SmtExpr>,
    ) -> Result<Answer, DebugError> {
        self.solver.push()?;
        let run = || -> Result<SmtSolverResponse, DebugError> {
            for e in extra {
                self.solver.write_smt(SmtAssert(e))?;
            }
            Ok(self.solver.check_sat()?)
        };
        let response = run();
        self.solver.pop()?;
        let answer = Answer::from(response?);
        answers.push(SolverAnswer {
            query: query.into(),
            answer,
        });
        Ok(answer)
    }

    // -- the decision ------------------------------------------------------

    /// Decide the node: which rule applies, and the child states. Returns the
    /// views of both sides and the solver answers with it.
    #[allow(clippy::type_complexity)]
    fn decide(
        &mut self,
        joint: &mut Joint<'a>,
    ) -> Result<(Decided<'a>, (SideView, SideView, Vec<SolverAnswer>)), DebugError> {
        let left_view = side_view(&mut joint.left);
        let right_view = side_view(&mut joint.right);
        let mut answers = Vec::new();

        let both_terminal = matches!(
            (&joint.left.head, &joint.right.head),
            (Head::Terminal(_), Head::Terminal(_))
        );
        let any_branch = matches!(joint.left.head, Head::Branch(_))
            || matches!(joint.right.head, Head::Branch(_));

        let decided = if both_terminal {
            self.terminal_pair(joint)?
        } else {
            let plan = if any_branch {
                self.decide_branch(joint, &mut answers)?
            } else {
                self.decide_sampling(joint, &mut answers)?
            };
            Decided::Plan { plan, pair: None }
        };
        Ok((decided, (left_view, right_view, answers)))
    }

    fn decide_branch(
        &mut self,
        joint: &Joint<'a>,
        answers: &mut Vec<SolverAnswer>,
    ) -> Result<Plan<'a>, DebugError> {
        let branch_of = |s: &SideState<'a>| match &s.head {
            Head::Branch(b) => Some(b.clone()),
            _ => None,
        };
        let left = branch_of(&joint.left);
        let right = branch_of(&joint.right);

        // 1. a determined branch goes alone, left before right
        for (side, branch) in [(Side::Left, &left), (Side::Right, &right)] {
            let Some(branch) = branch else { continue };
            let name = side_name(side);
            let (first, second) = branch.decisions();
            let first_possible = self.ask(
                answers,
                format!("{name}-{}-possible", first.as_str()),
                vec![branch.cond.clone()],
            )? != Answer::Unsat;
            let second_possible = self.ask(
                answers,
                format!("{name}-{}-possible", second.as_str()),
                vec![SmtNot(branch.cond.clone()).into()],
            )? != Answer::Unsat;
            let taken = match (first_possible, second_possible) {
                (false, false) => {
                    return Ok(Plan {
                        kind: NodeKind::Unreachable,
                        children: Vec::new(),
                        stuck: None,
                    })
                }
                (true, false) => first,
                (false, true) => second,
                (true, true) => continue,
            };
            let mut child = joint.clone();
            let step = self.take_branch(&mut child, side, branch, taken);
            let (left_step, right_step) = steps_for(side, step);
            return Ok(Plan {
                kind: NodeKind::Determined,
                children: vec![PlannedChild {
                    left: left_step,
                    right: right_step,
                    joint: child,
                    check_feasible: false,
                }],
                stuck: None,
            });
        }

        // 2. equivalent conditions: both go the same way
        if let (Some(l), Some(r)) = (&left, &right) {
            let differ: SmtExpr = SmtNot(SmtEq2 {
                lhs: l.cond.clone(),
                rhs: r.cond.clone(),
            })
            .into();
            if self.ask(answers, "branches-differ", vec![differ])? == Answer::Unsat {
                let (l_first, l_second) = l.decisions();
                let (r_first, r_second) = r.decisions();
                let mut children = Vec::new();
                for (ld, rd) in [(l_first, r_first), (l_second, r_second)] {
                    let mut child = joint.clone();
                    let ls = self.take_branch(&mut child, Side::Left, l, ld);
                    let rs = self.take_branch(&mut child, Side::Right, r, rd);
                    children.push(PlannedChild {
                        left: Some(ls),
                        right: Some(rs),
                        joint: child,
                        check_feasible: false,
                    });
                }
                return Ok(Plan {
                    kind: NodeKind::Synchronized,
                    children,
                    stuck: None,
                });
            }
        }

        // 3. split: every combination, then before else, left before right
        let mut children = Vec::new();
        match (&left, &right) {
            (Some(l), Some(r)) => {
                let (l_first, l_second) = l.decisions();
                let (r_first, r_second) = r.decisions();
                for ld in [l_first, l_second] {
                    for rd in [r_first, r_second] {
                        let mut child = joint.clone();
                        let ls = self.take_branch(&mut child, Side::Left, l, ld);
                        let rs = self.take_branch(&mut child, Side::Right, r, rd);
                        children.push(PlannedChild {
                            left: Some(ls),
                            right: Some(rs),
                            joint: child,
                            check_feasible: true,
                        });
                    }
                }
            }
            (one, other) => {
                let (side, branch) = match (one, other) {
                    (Some(l), None) => (Side::Left, l),
                    (None, Some(r)) => (Side::Right, r),
                    _ => unreachable!("decide_branch is called with a branch on some side"),
                };
                let (first, second) = branch.decisions();
                for d in [first, second] {
                    let mut child = joint.clone();
                    let step = self.take_branch(&mut child, side, branch, d);
                    let (left_step, right_step) = steps_for(side, step);
                    children.push(PlannedChild {
                        left: left_step,
                        right: right_step,
                        joint: child,
                        check_feasible: true,
                    });
                }
            }
        }
        Ok(Plan {
            kind: NodeKind::Split,
            children,
            stuck: None,
        })
    }

    fn decide_sampling(
        &mut self,
        joint: &Joint<'a>,
        answers: &mut Vec<SolverAnswer>,
    ) -> Result<Plan<'a>, DebugError> {
        let sample_of = |s: &SideState<'a>| match &s.head {
            Head::Sample(x) => Some(x.clone()),
            _ => None,
        };
        let left = sample_of(&joint.left);
        let right = sample_of(&joint.right);

        // synchronized: the two draws are equal under A ∧ pc
        if let (Some(l), Some(r)) = (&left, &right) {
            if l.ty.types_match(&r.ty) {
                let differ: SmtExpr = SmtNot(SmtEq2 {
                    lhs: l.term.clone(),
                    rhs: r.term.clone(),
                })
                .into();
                if self.ask(answers, "draws-differ", vec![differ])? == Answer::Unsat {
                    let mut child = joint.clone();
                    let ls = self.take_sample(&mut child, Side::Left, l);
                    let rs = self.take_sample(&mut child, Side::Right, r);
                    return Ok(Plan {
                        kind: NodeKind::SamplingSynchronized,
                        children: vec![PlannedChild {
                            left: Some(ls),
                            right: Some(rs),
                            joint: child,
                            check_feasible: false,
                        }],
                        stuck: None,
                    });
                }
            }
        }

        // otherwise each side's sampling on its own; independent ones go alone,
        // left first, and the first stuck one is admitted
        let mut first_stuck: Option<(Side, SampleHead<'a>, StuckReason)> = None;
        for (side, sample) in [(Side::Left, &left), (Side::Right, &right)] {
            let Some(sample) = sample else { continue };
            let other_ended = matches!(joint.side(other(side)).head, Head::Terminal(_));
            match self.classify(side, sample, other_ended, answers)? {
                Classification::Independent => {
                    let mut child = joint.clone();
                    let step = self.take_sample(&mut child, side, sample);
                    let (left_step, right_step) = steps_for(side, step);
                    return Ok(Plan {
                        kind: NodeKind::SamplingIndependent,
                        children: vec![PlannedChild {
                            left: left_step,
                            right: right_step,
                            joint: child,
                            check_feasible: false,
                        }],
                        stuck: None,
                    });
                }
                Classification::Stuck(reason) => {
                    first_stuck.get_or_insert((side, sample.clone(), reason));
                }
            }
        }
        let (side, sample, reason) =
            first_stuck.expect("a node with no branch and not two terminals has a sampling");
        let mut child = joint.clone();
        let step = self.take_sample(&mut child, side, &sample);
        let (left_step, right_step) = steps_for(side, step);
        let name = self.exec(side).sample_name(sample.sample_id);
        Ok(Plan {
            kind: NodeKind::Stuck,
            children: vec![PlannedChild {
                left: left_step,
                right: right_step,
                joint: child,
                check_feasible: false,
            }],
            stuck: Some(StuckDraft {
                side,
                label: sample.label,
                sample: name,
                draw: sample.ctr,
                reason,
            }),
        })
    }

    /// Is the sampling independent: does the randomness mapping pair it with
    /// nothing, under `A ∧ pc`? If not, why can EasyCrypt not be handed a step?
    fn classify(
        &mut self,
        side: Side,
        sample: &SampleHead<'a>,
        other_ended: bool,
        answers: &mut Vec<SolverAnswer>,
    ) -> Result<Classification, DebugError> {
        let name = side_name(side);
        let premises: Vec<SmtExpr> = self
            .terms
            .pairings
            .iter()
            .filter(|p| match side {
                Side::Left => p.left_sample == sample.sample_id && p.offset_left == sample.ctr,
                Side::Right => p.right_sample == sample.sample_id && p.offset_right == sample.ctr,
            })
            .map(|p| p.premise.clone())
            .collect();
        if premises.is_empty() {
            return Ok(Classification::Independent);
        }

        let any: SmtExpr = SmtOr(premises.clone()).into();
        if self.ask(answers, format!("{name}-pairing-possible"), vec![any])? == Answer::Unsat {
            return Ok(Classification::Independent);
        }

        // Some premise may hold. Which kind of "may" decides the reason.
        let (mut live, mut unknown, mut valid) = (false, false, false);
        for (i, premise) in premises.iter().enumerate() {
            match self.ask(
                answers,
                format!("{name}-pairing-{i}-possible"),
                vec![premise.clone()],
            )? {
                Answer::Unsat => {}
                Answer::Unknown => (live, unknown) = (true, true),
                Answer::Sat => {
                    live = true;
                    let negated = vec![SmtNot(premise.clone()).into()];
                    match self.ask(answers, format!("{name}-pairing-{i}-valid"), negated)? {
                        Answer::Unsat => valid = true,
                        Answer::Unknown => unknown = true,
                        Answer::Sat => {}
                    }
                }
            }
        }
        Ok(if !live {
            // the disjunction was undecided, but every premise is not
            Classification::Independent
        } else if unknown {
            Classification::Stuck(StuckReason::PairingUnknown)
        } else if valid && other_ended {
            Classification::Stuck(StuckReason::NoPartnerReachable)
        } else if valid {
            Classification::Stuck(StuckReason::PartnerNotAtHead)
        } else {
            Classification::Stuck(StuckReason::PairingSatNotValid)
        })
    }

    fn take_branch(
        &mut self,
        joint: &mut Joint<'a>,
        side: Side,
        head: &BranchHead<'a>,
        decision: Decision,
    ) -> SideStep {
        let (exec, state) = match side {
            Side::Left => (&mut self.left, &mut joint.left),
            Side::Right => (&mut self.right, &mut joint.right),
        };
        state.head = exec.take_branch(&mut state.pos, head, decision);
        SideStep {
            label: head.label,
            decision: decision.as_str().to_string(),
        }
    }

    fn take_sample(
        &mut self,
        joint: &mut Joint<'a>,
        side: Side,
        head: &SampleHead<'a>,
    ) -> SideStep {
        let (exec, state) = match side {
            Side::Left => (&mut self.left, &mut joint.left),
            Side::Right => (&mut self.right, &mut joint.right),
        };
        state.head = exec.take_sample(&mut state.pos, head);
        SideStep {
            label: head.label,
            decision: "draw".to_string(),
        }
    }

    // -- terminal pairs ----------------------------------------------------

    fn terminal_pair(&mut self, joint: &Joint<'a>) -> Result<Decided<'a>, DebugError> {
        if let Some(limit) = self.opts.max_paths {
            if self.out.pairs.len() >= limit {
                self.out.stop_reason = StopReason::MaxPaths { limit };
                return Ok(Decided::Stop);
            }
        }
        let (Head::Terminal(left_terminal), Head::Terminal(right_terminal)) =
            (&joint.left.head, &joint.right.head)
        else {
            unreachable!("terminal_pair is called with two terminals");
        };
        let started = Instant::now();
        let left_path = self.left.terminal_path(&joint.left.pos, left_terminal);
        let right_path = self.right.terminal_path(&joint.right.pos, right_terminal);
        let id = format!("J{}", self.out.pairs.len() + 1);

        self.solver.push()?;
        let checks = self.check_pair(&id, &left_path, &right_path);
        self.solver.pop()?;
        let claims = checks?;

        let record = PairRecord {
            id,
            node: 0,
            left: pair_side(self.left_inlined, &left_path),
            right: pair_side(self.right_inlined, &right_path),
            claims,
        };
        Ok(Decided::Plan {
            plan: Plan {
                kind: NodeKind::TerminalPair,
                children: Vec::new(),
                stuck: None,
            },
            pair: Some((record, left_path, right_path, started.elapsed())),
        })
    }

    /// The vacuity check, then each claim on its own dependencies and negated goal, and, when
    /// the `invariant` is not verified, each state relation.
    fn check_pair(
        &mut self,
        id: &str,
        left: &TerminalPath,
        right: &TerminalPath,
    ) -> Result<Vec<ClaimVerdict>, DebugError> {
        for path in [left, right] {
            for e in path.decls[path.reported_decls..]
                .iter()
                .chain(&path.constraints[path.reported_constraints..])
            {
                self.solver.write_smt(e.clone())?;
            }
            self.solver.write_smt(path.return_constraint.clone())?;
        }

        let terms = self.terms;
        // unconditional: `unsat` means the pair cannot happen, which is not
        // the same as verified
        if matches!(self.solver.check_sat()?, SmtSolverResponse::Unsat) {
            return Ok(terms
                .claims
                .iter()
                .map(|claim| ClaimVerdict {
                    claim: claim.name.clone(),
                    verdict: Verdict::pair_infeasible(),
                    relations: Vec::new(),
                })
                .collect());
        }

        let aborts = PairAborts {
            left: left.terminal.is_abort(),
            right: right.terminal.is_abort(),
        };
        let mut checked = Vec::with_capacity(terms.claims.len());
        for claim in &terms.claims {
            let mut queries = 0;
            let (verdict, _) = check_claim(
                &mut *self.solver,
                claim,
                aborts,
                self.opts.out_dir,
                self.opts.layout,
                &format!("{id}.{}", claim.name),
                &mut queries,
            )?;
            let mut relations = Vec::new();
            if claim.name == "invariant"
                && !matches!(verdict, Verdict::Verified | Verdict::Unreachable { .. })
            {
                for relation in &terms.relations {
                    let verdict = self.check_goal(
                        &relation.negated,
                        id,
                        &format!("relation-{}", relation.name),
                    )?;
                    relations.push(RelationVerdict {
                        name: relation.name.clone(),
                        verdict,
                    });
                }
            }
            checked.push(ClaimVerdict {
                claim: claim.name.clone(),
                verdict,
                relations,
            });
        }
        Ok(checked)
    }

    /// Assert one negated goal and classify the answer. A model of a failing
    /// check goes to `models/<id>.<check>.smt2`.
    fn check_goal(
        &mut self,
        negated: &SmtExpr,
        id: &str,
        check: &str,
    ) -> Result<Verdict, DebugError> {
        self.solver.push()?;
        let verdict = (|| -> Result<Verdict, DebugError> {
            self.solver.write_smt(negated.clone())?;
            let model_id = format!("{id}.{check}");
            Ok(match self.solver.check_sat()? {
                SmtSolverResponse::Unsat => Verdict::Verified,
                SmtSolverResponse::Sat => {
                    let (model, _) = write_model(&mut *self.solver, self.opts.out_dir, self.opts.layout, &model_id)?;
                    Verdict::GoalFails { model }
                }
                SmtSolverResponse::Unknown => {
                    match write_model(&mut *self.solver, self.opts.out_dir, self.opts.layout, &model_id) {
                        Ok((model, _)) => Verdict::Inconclusive { model: Some(model) },
                        Err(_) => Verdict::Inconclusive { model: None },
                    }
                }
            })
        })();
        self.solver.pop()?;
        verdict
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn side_name(side: Side) -> &'static str {
    match side {
        Side::Left => "left",
        Side::Right => "right",
    }
}

fn other(side: Side) -> Side {
    match side {
        Side::Left => Side::Right,
        Side::Right => Side::Left,
    }
}

/// `step` placed on the side that took it.
fn steps_for(side: Side, step: SideStep) -> (Option<SideStep>, Option<SideStep>) {
    match side {
        Side::Left => (Some(step), None),
        Side::Right => (None, Some(step)),
    }
}

fn head_label(head: &Head<'_>) -> usize {
    match head {
        Head::Branch(b) => b.label,
        Head::Sample(s) => s.label,
        Head::Terminal(t) => t.label(),
    }
}

/// Describe where a side stands, and report its consumption so far.
fn side_view(state: &mut SideState<'_>) -> SideView {
    let (kind, plumbing) = match &state.head {
        Head::Branch(b) => (
            match b.form {
                BranchForm::If { .. } => HeadKind::Branch,
                BranchForm::Unwrap { .. } => HeadKind::Unwrap,
            },
            b.plumbing().map(PlumbingKind::from),
        ),
        Head::Sample(_) => (HeadKind::Sample, None),
        Head::Terminal(Terminal::Return { .. }) => (HeadKind::Return, None),
        Head::Terminal(Terminal::Abort { .. }) => (HeadKind::Abort, None),
    };
    let view = SideView {
        head: HeadView {
            kind,
            label: head_label(&state.head),
        },
        consumed: lines_view(&state.pos.consumed()),
        plumbing,
    };
    state.pos.commit_consumed();
    view
}

fn pair_side(inlined: &InlinedOracle, path: &TerminalPath) -> PairSide {
    PairSide {
        steps: steps_view(&inlined.listing, &path.steps),
        terminal: terminal_view(&inlined.listing, &path.terminal),
        lines: lines_view(&path.lines),
        effect: path.effect.clone(),
    }
}
