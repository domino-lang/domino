// SPDX-License-Identifier: MIT OR Apache-2.0

//! The prover: walks the lockstep joint tree of one oracle depth first, alongside a live
//! EasyCrypt session, and writes down the sentences EasyCrypt accepts (story 27 §3.2-§3.6).
//!
//! **Invariant of the walk.** Every routine that handles "the front goal" leaves the session in
//! the state "that goal is closed and every other goal is as it was": what a tactic produces is
//! handled front to back, each subgoal in its own bullet. A subgoal EasyCrypt could not be
//! made to close is closed with a labelled `admit`. Every attempt runs under `undo`: the
//! session is always "all accepted sentences so far", so the script replays.
//!
//! **Tactics take positions from EasyCrypt** (ADR 0002): the joint tree supplies decisions
//! only. Counts for `sp k l` and the names of sampled variables are read from the JSON of the
//! goal in front, and subgoals are told apart by kind, never by position in a list.

use std::collections::HashMap;
use std::time::Duration;

use crate::debug::driver::Verdict;
use crate::debug::lockstep::{
    ChildOutcome, HeadKind, JointChild, JointNode, LockstepOutcome, NodeKind, PairRecord,
};
use crate::easycrypt::json::{Goal, Status};
use crate::easycrypt::session::{Session, SessionError};

use super::goals;
use super::live::LiveHandle;
use super::script::{Mark, Script};

type R<T> = Result<T, SessionError>;

/// Why an `admit` is there (story 27 §3.7). The slugs are what the report counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdmitReason {
    /// The lockstep engine could not decide a sampling.
    Stuck,
    /// A claim fails in Domino, so EasyCrypt was not asked.
    DominoFails,
    /// Domino could not decide, and EasyCrypt could not either.
    DominoInconclusive,
    /// Domino verified the claim and EasyCrypt could not close it: where better heuristics pay
    /// off, and story 29's input.
    DominoVerifiedEcFailed,
    /// EasyCrypt's program did not match what the lowering said, and the fallback found nothing.
    ProgramMismatch,
    /// A sampling that `seq` could not be given a safe postcondition for.
    SeqPost,
    /// A goal of the router prelude (the condition, or both sides already aborted).
    Router,
    /// A goal still open when the oracle was sealed (story 33): the walk had not got to it
    /// when the file was written.
    Interrupted,
}

impl AdmitReason {
    pub const ALL: [AdmitReason; 8] = [
        AdmitReason::Stuck,
        AdmitReason::DominoFails,
        AdmitReason::DominoInconclusive,
        AdmitReason::DominoVerifiedEcFailed,
        AdmitReason::ProgramMismatch,
        AdmitReason::SeqPost,
        AdmitReason::Router,
        AdmitReason::Interrupted,
    ];

    pub fn slug(self) -> &'static str {
        match self {
            AdmitReason::Stuck => "stuck",
            AdmitReason::DominoFails => "domino-fails",
            AdmitReason::DominoInconclusive => "domino-inconclusive",
            AdmitReason::DominoVerifiedEcFailed => "domino-verified-ec-failed",
            AdmitReason::ProgramMismatch => "program-mismatch",
            AdmitReason::SeqPost => "seq-post",
            AdmitReason::Router => "router",
            AdmitReason::Interrupted => "interrupted",
        }
    }
}

/// What Domino itself concluded about the claim an admit stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DominoView {
    Verified,
    Fails,
    Inconclusive,
    /// Domino has no verdict for it (the router prelude).
    NotApplicable,
}

impl DominoView {
    pub fn slug(self) -> &'static str {
        match self {
            DominoView::Verified => "verified",
            DominoView::Fails => "fails",
            DominoView::Inconclusive => "inconclusive",
            DominoView::NotApplicable => "n/a",
        }
    }

    fn worst(self, other: DominoView) -> DominoView {
        use DominoView::*;
        match (self, other) {
            (Fails, _) | (_, Fails) => Fails,
            (Inconclusive, _) | (_, Inconclusive) => Inconclusive,
            _ => self,
        }
    }
}

/// One `admit` in the script.
#[derive(Debug, Clone)]
pub struct Admit {
    pub reason: AdmitReason,
    /// `J<n>` (a joint path), `S<n>` (a stuck point), `N<n>` (a node of the joint tree) or
    /// `router`.
    pub id: String,
    /// `equal-output`, `invariant`, `invariant/Domino_<rel>`, `side-goal`, …
    pub claim: String,
    pub domino: DominoView,
    /// The goal as EasyCrypt prints it on one line.
    pub goal: String,
}

impl Admit {
    /// The comment after the `admit.`: `(* domino: J7 invariant/Domino_rel; reason: <slug>;
    /// Domino: verified *)`.
    pub fn label(&self) -> String {
        format!(
            "(* domino: {} {}; reason: {}; Domino: {} *)",
            self.id,
            self.claim,
            self.reason.slug(),
            self.domino.slug()
        )
    }
}

/// What happened while proving one oracle.
#[derive(Debug, Clone, Default)]
pub struct OracleStats {
    /// Goals closed by a tactic other than `admit`.
    pub closed: usize,
    pub admits: Vec<Admit>,
    /// Nodes that used the fallback trial procedure (§3.4).
    pub fallbacks: usize,
    /// Sentences EasyCrypt refused or that were undone.
    pub attempts_undone: usize,
}

/// The joint tree of an oracle with what the walk needs to know about each node's subtree.
pub(super) struct OracleTree<'a> {
    pub outcome: &'a LockstepOutcome,
    /// Indices into `outcome.pairs` of the pairs at or below each node.
    subtree: Vec<Vec<usize>>,
    pair_of_node: HashMap<usize, usize>,
}

impl<'a> OracleTree<'a> {
    pub(super) fn new(outcome: &'a LockstepOutcome) -> OracleTree<'a> {
        let nodes = &outcome.tree.nodes;
        let mut pair_of_node = HashMap::new();
        for (i, pair) in outcome.pairs.iter().enumerate() {
            pair_of_node.insert(pair.node, i);
        }
        // pre-order arena: a child always has a larger index than its parent
        let mut subtree: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
        for idx in (0..nodes.len()).rev() {
            let mut below = Vec::new();
            if let Some(&p) = pair_of_node.get(&idx) {
                below.push(p);
            }
            for child in &nodes[idx].children {
                if let ChildOutcome::Explored { node } = child.outcome {
                    below.extend(subtree[node].iter().copied());
                }
            }
            below.sort_unstable();
            subtree[idx] = below;
        }
        OracleTree {
            outcome,
            subtree,
            pair_of_node,
        }
    }

    fn node(&self, idx: usize) -> &'a JointNode {
        &self.outcome.tree.nodes[idx]
    }

    fn pairs_below(&self, idx: usize) -> impl Iterator<Item = &'a PairRecord> + '_ {
        self.subtree
            .get(idx)
            .into_iter()
            .flatten()
            .map(|&i| &self.outcome.pairs[i])
    }
}

/// Which claim a part of a goal stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Part {
    /// A whole goal, or one whose meaning has not been told apart yet.
    Whole,
    EqualOutput,
    Invariant,
    /// A state relation, by the name of its `define-state-relation`.
    Relation(String),
}

impl Part {
    fn claim_label(&self) -> String {
        match self {
            Part::Whole => "equal-output+invariant".into(),
            Part::EqualOutput => "equal-output".into(),
            Part::Invariant => "invariant".into(),
            Part::Relation(name) => format!("invariant/Domino_{name}"),
        }
    }
}

fn view_of_verdict(verdict: &Verdict) -> DominoView {
    match verdict {
        Verdict::Verified | Verdict::Unreachable => DominoView::Verified,
        Verdict::GoalFails { .. } => DominoView::Fails,
        Verdict::Inconclusive { .. } => DominoView::Inconclusive,
    }
}

fn pair_aborts(pair: &PairRecord) -> bool {
    pair.left.terminal.is_abort || pair.right.terminal.is_abort
}

/// What Domino says about `part` on one pair. On a pair where a side aborts, an invariant
/// failure is not held against EasyCrypt (story 23's note: Domino's verdict is stricter there
/// than EasyCrypt's `inv`), so it counts as inconclusive.
pub(super) fn pair_view(pair: &PairRecord, part: &Part) -> DominoView {
    let invariant = |v: &Verdict| {
        let view = view_of_verdict(v);
        if view == DominoView::Fails && pair_aborts(pair) {
            DominoView::Inconclusive
        } else {
            view
        }
    };
    match part {
        Part::EqualOutput => view_of_verdict(&pair.equal_output),
        Part::Invariant => invariant(&pair.invariant),
        Part::Relation(name) => pair
            .relations
            .iter()
            .find(|r| &r.name == name)
            .map_or_else(|| invariant(&pair.invariant), |r| invariant(&r.verdict)),
        Part::Whole => view_of_verdict(&pair.equal_output).worst(invariant(&pair.invariant)),
    }
}

/// The lemmas every `smt(…)` of the last rungs is given (§3.5 step 5); the project's own come
/// from `ssp.toml`.
const BASE_SMT_LEMMAS: [&str; 3] = ["get_setE", "mem_set", "emptyE"];

/// Timeouts of the prover.
#[derive(Debug, Clone, Copy)]
pub struct Timeouts {
    /// Every sentence but rung 0.
    pub general: Duration,
    /// Rung 0 (`auto => /#.` on every program goal): short.
    pub rung0: Duration,
}

/// An oracle's proof as it stands, sealed (story 33): the script with every goal still open
/// closed by an `admit` labelled `interrupted`, the stats counting those admits, and the
/// alignment's mismatches so far.
pub(super) struct Sealed {
    pub script: String,
    pub stats: OracleStats,
    pub mismatches: Vec<String>,
    /// The joint node the walk was in, as the `interrupted` admits name it: `N<k>` or `router`.
    pub node: String,
}

/// A point to return to: the session's state and the script's.
struct Snap {
    state: u64,
    script: Mark,
    closed: usize,
}

pub(super) struct Prover<'a> {
    pub session: &'a mut Session,
    pub script: Script,
    pub tree: &'a OracleTree<'a>,
    pub hints: &'a [String],
    /// The operators of the invariant file, `inv`, `params_inv` and `Domino_<rel>`, in the order
    /// `rewrite /… in` unfolds them.
    pub unfold_ops: &'a [String],
    pub timeouts: Timeouts,
    /// Rung 0 (`auto => /#.` on every program goal) is on unless a test turns it off to
    /// exercise the walk.
    pub rung0: bool,
    /// The exported oracle, for the transcript's notes.
    pub oracle: &'a str,
    /// The most time splitting one leaf by meaning may take: every sentence of a deep goal
    /// costs seconds (EasyCrypt prints all open goals as JSON), and a leaf has a dozen parts.
    pub leaf_budget: Duration,
    /// When the current leaf's budget runs out.
    pub deadline: Option<std::time::Instant>,
    pub stats: OracleStats,
    /// The live translation page (story 28), told which node and rung the walk is at.
    pub live: Option<LiveHandle>,
    /// Called with the sealed oracle after every joint node (`--write-granularity node`).
    pub checkpoint: Option<&'a mut dyn FnMut(Sealed)>,
    /// The joint node being proved, innermost (`None` in the router prelude).
    pub node: Option<usize>,
    /// The descriptions of the alignment's mismatches: with any, the oracle is proved by the
    /// fallback.
    pub mismatches: Vec<String>,
    /// The oracle sealed where the walk stood when it saw that the run was asked to stop
    /// (Ctrl-C, story 34); the walk then unwinds with [`SessionError::Stopped`].
    pub stopped: Option<Sealed>,
}

impl Prover<'_> {
    // ------------------------------------------------------------------
    // Session primitives
    // ------------------------------------------------------------------

    pub(super) fn count(&self) -> usize {
        self.session.goals().len()
    }

    // ------------------------------------------------------------------
    // The seal (story 33)
    // ------------------------------------------------------------------

    /// The oracle sealed where the walk stands: every goal it still has open is admitted, with
    /// the reason `interrupted` and the joint node the walk is in. Sends nothing to EasyCrypt,
    /// and the walk goes on from the unsealed script. Between two sentences is any time.
    pub(super) fn seal(&self) -> Sealed {
        self.seal_with(self.count())
    }

    /// [`Self::seal`], with `open` goals open in the session.
    fn seal_with(&self, open: usize) -> Sealed {
        let admit = Admit {
            reason: AdmitReason::Interrupted,
            id: self
                .node
                .map_or_else(|| "router".to_string(), |n| format!("N{n}")),
            claim: "open-goal".into(),
            domino: DominoView::NotApplicable,
            goal: String::new(),
        };
        let (script, admits) = self.script.sealed(open, &admit.label());
        let node = admit.id.clone();
        let mut stats = self.stats.clone();
        stats.admits.extend(std::iter::repeat_n(admit, admits));
        Sealed {
            script: script.render(),
            stats,
            mismatches: self.mismatches.clone(),
            node,
        }
    }

    // ------------------------------------------------------------------
    // Ctrl-C (story 34)
    // ------------------------------------------------------------------

    /// Where the walk stops if the run was asked to stop: the oracle is sealed as it stands
    /// ([`Self::stopped`]) and [`SessionError::Stopped`] unwinds the walk, ladders and leaf
    /// splits included. Called before every sentence the walk sends, so after an interrupted
    /// sentence has been rolled back like any failed attempt. The seal reads only the script and
    /// the goal count, which agree between any two sentences.
    fn stop_point(&mut self) -> R<()> {
        if !self.session.stop_requested() {
            return Ok(());
        }
        Err(self.stop_with(self.count()))
    }

    /// Seals the oracle with `open` goals open, unless it is sealed already, and returns
    /// [`SessionError::Stopped`].
    fn stop_with(&mut self, open: usize) -> SessionError {
        if self.stopped.is_none() {
            self.stopped = Some(self.seal_with(open));
        }
        SessionError::Stopped
    }

    /// `e`, unless the run was asked to stop: EasyCrypt not answering the interrupt then is a
    /// stop like any other, with what has been proved so far.
    fn session_failed(&mut self, e: SessionError) -> SessionError {
        if matches!(e, SessionError::Unresponsive { .. }) && self.session.stop_requested() {
            return self.stop_point().expect_err("a stop was requested");
        }
        e
    }

    /// Seals the oracle and hands it to the checkpoint, if there is one.
    fn checkpoint(&mut self) {
        if self.checkpoint.is_none() {
            return;
        }
        let sealed = self.seal();
        if let Some(checkpoint) = self.checkpoint.as_mut() {
            checkpoint(sealed);
        }
    }

    fn front(&self) -> Option<&Goal> {
        self.session.goals().first()
    }

    fn state(&self) -> u64 {
        self.session.last().map_or(0, |r| r.state)
    }

    fn snap(&self) -> Snap {
        Snap {
            state: self.state(),
            script: self.script.mark(),
            closed: self.stats.closed,
        }
    }

    fn rollback(&mut self, snap: Snap) -> R<()> {
        if self.state() != snap.state {
            if let Err(e) = self.session.undo_to(snap.state) {
                return Err(self.session_failed(e));
            }
        }
        self.script.rollback(snap.script);
        self.stats.closed = snap.closed;
        self.stats.attempts_undone += 1;
        Ok(())
    }

    /// Sends one sentence; an accepted one goes into the script. `Ok(false)` if EasyCrypt
    /// refused it (or it was interrupted): the session is then where it was.
    pub(super) fn send(&mut self, sentence: &str) -> R<bool> {
        self.stop_point()?;
        let before = self.count();
        let ok = match self.session.send(sentence) {
            // the sentence a stop interrupted lost its goals: stop as if it had not been sent
            Ok(response) if response.goals_lost() => return Err(self.stop_with(before)),
            Ok(response) => response.status == Status::Ok,
            Err(e) => return Err(self.session_failed(e)),
        };
        if ok {
            self.script.push(sentence, None);
            let after = self.count();
            if after < before {
                self.stats.closed += before - after;
            }
        }
        Ok(ok)
    }

    /// Sends the sentences in order and keeps them if all are accepted and `want` holds at the
    /// end; otherwise everything is undone.
    fn attempt(&mut self, sentences: &[&str], want: impl Fn(&Self) -> bool) -> R<bool> {
        let snap = self.snap();
        for sentence in sentences {
            if !self.send(sentence)? {
                self.rollback(snap)?;
                return Ok(false);
            }
        }
        if !want(self) {
            self.rollback(snap)?;
            return Ok(false);
        }
        Ok(true)
    }

    /// An attempt that must close the front goal.
    fn try_close(&mut self, sentences: &[&str]) -> R<bool> {
        let before = self.count();
        self.attempt(sentences, |p| p.count() + 1 == before)
    }

    fn with_timeout<T>(&mut self, timeout: Duration, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let saved = self.session.timeout();
        self.session.set_timeout(timeout);
        let result = f(self);
        self.session.set_timeout(saved);
        result
    }

    /// Runs `f` as the block of the next subgoal: its first sentence gets the bullet.
    fn bullet<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.script.enter_bullet(self.count());
        let result = f(self);
        self.script.leave_bullet();
        result
    }

    // ------------------------------------------------------------------
    // Admits
    // ------------------------------------------------------------------

    /// Closes the front goal with a labelled `admit`.
    fn admit(&mut self, reason: AdmitReason, id: &str, claim: &str, domino: DominoView) -> R<()> {
        let goal_pp = self
            .front()
            .map(|g| g.concl.pp.replace('\n', " "))
            .unwrap_or_default();
        let admit = Admit {
            reason,
            id: id.to_string(),
            claim: claim.to_string(),
            domino,
            goal: goal_pp,
        };
        let label = admit.label();
        self.stop_point()?;
        let before = self.count();
        let response = match self.session.send("admit.") {
            Ok(response) if response.goals_lost() => return Err(self.stop_with(before)),
            Ok(response) => response,
            Err(e) => return Err(self.session_failed(e)),
        };
        if response.status != Status::Ok {
            let msg = response
                .error
                .as_ref()
                .map_or_else(|| format!("{:?}", response.status), |e| e.msg.clone());
            // interrupted by a stop request
            self.stop_point()?;
            // `admit.` closes any goal: a refusal means there is none, and the walk is lost
            return Err(SessionError::Refused {
                sentence: "admit.".into(),
                msg,
            });
        }
        self.script.push("admit.", Some(label));
        if let Some(live) = &self.live {
            live.admitted(&admit);
        }
        self.stats.admits.push(admit);
        Ok(())
    }

    /// The first pair below `node` for which `part` has the given view, else its first pair.
    fn id_below(&self, node: usize, part: &Part, view: DominoView) -> String {
        let tree = self.tree;
        let pick = tree
            .pairs_below(node)
            .find(|p| pair_view(p, part) == view)
            .or_else(|| tree.pairs_below(node).next());
        match pick {
            Some(pair) => pair.id.clone(),
            None => format!("N{node}"),
        }
    }

    /// Admits after EasyCrypt failed on `part` of the subtree at `node`: the reason is what
    /// Domino itself concluded (§3.6).
    fn admit_ec_failed(&mut self, node: usize, part: &Part, claim: &str) -> R<()> {
        let tree = self.tree;
        let view = if tree.subtree.get(node).is_none_or(|below| below.is_empty()) {
            DominoView::Inconclusive
        } else {
            tree.pairs_below(node)
                .map(|p| pair_view(p, part))
                .fold(DominoView::Verified, DominoView::worst)
        };
        let reason = match view {
            DominoView::Fails => AdmitReason::DominoFails,
            DominoView::Inconclusive | DominoView::NotApplicable => AdmitReason::DominoInconclusive,
            DominoView::Verified => AdmitReason::DominoVerifiedEcFailed,
        };
        let id = self.id_below(node, part, view);
        self.admit(reason, &id, claim, view)
    }

    // ------------------------------------------------------------------
    // Closing ambient goals: side goals, the ladder
    // ------------------------------------------------------------------

    /// Brings the front goal to a plain formula: introduces the memory of a quantified program
    /// judgement (`forall &m0, hoare[…]`, what `rcondt` leaves as its side goal) and reduces a
    /// program judgement with nothing left to do (`<skip>`) by `auto.`
    fn reduce_to_ambient(&mut self) -> R<()> {
        for _ in 0..4 {
            let step = {
                let Some(goal) = self.front() else {
                    return Ok(());
                };
                let c = &goal.concl;
                if goals::wraps_program(c) {
                    goals::as_forall(c).map(|(names, _)| format!("move => {}.", names.join(" ")))
                } else if !goals::is_ambient(goal) {
                    Some("auto.".to_string())
                } else {
                    None
                }
            };
            let Some(sentence) = step else { return Ok(()) };
            let before = self.count();
            if !self.attempt(&[&sentence], |p| p.count() == before)? {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Unfolds the invariant's operators in the hypothesis `name` (`rewrite /inv /params_inv
    /// /Domino_… in name.`), so a solver sees through them; only if the hypothesis mentions
    /// `inv`. `Ok(false)` if there was nothing to unfold or EasyCrypt refused.
    fn unfold_premise(&mut self, name: &str) -> R<bool> {
        let mentions = self.front().is_some_and(|g| {
            g.hyps.iter().any(|h| {
                h.name == name
                    && h.form
                        .as_ref()
                        .is_some_and(|f| goals::mentions_op(f, "inv"))
            })
        });
        if !mentions {
            return Ok(false);
        }
        let all: String = self.unfold_ops.iter().map(|o| format!(" /{o}")).collect();
        for ops in [all.as_str(), " /inv"] {
            if self.send(&format!("rewrite{ops} in {name}."))? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// `move => <binders> hpre.`, the invariant unfolded in `hpre`, then `tail`.
    fn try_with_premise(&mut self, tail: &str) -> R<bool> {
        let intro = {
            let Some(goal) = self.front() else {
                return Ok(false);
            };
            match goals::as_forall(&goal.concl) {
                Some((names, body)) if goals::as_implication(body).is_some() => {
                    Some((names.join(" "), goals::fresh_name(goal, "hpre")))
                }
                _ => None,
            }
        };
        let Some((names, premise)) = intro else {
            return Ok(false);
        };
        let before = self.count();
        let snap = self.snap();
        if self.send(&format!("move => {names} {premise}."))? {
            self.unfold_premise(&premise)?;
            if self.send(tail)? && self.count() + 1 == before {
                return Ok(true);
            }
        }
        self.rollback(snap)?;
        Ok(false)
    }

    /// The ladder (§3.5): `smt()`, then the same with the premise introduced and the invariant
    /// unfolded in it (`/#` on a quantified goal), then the hint list likewise.
    fn ladder(&mut self) -> R<bool> {
        self.reduce_to_ambient()?;
        let hints = self.hint_sentence();
        for (i, tail) in ["smt().", hints.as_str()].into_iter().enumerate() {
            let hinted = if i == 0 { "" } else { " with hints" };
            self.note_rung(&format!("ladder: {}", tail.trim_end_matches('.')));
            if self.try_close(&[tail])? {
                return Ok(true);
            }
            self.note_rung(&format!("ladder: premise unfolded, smt{hinted}"));
            if self.try_with_premise(tail)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn note_rung(&self, name: &str) {
        if let Some(live) = &self.live {
            live.rung(name);
        }
    }

    fn hint_sentence(&self) -> String {
        let mut names: Vec<&str> = BASE_SMT_LEMMAS.to_vec();
        names.extend(self.hints.iter().map(String::as_str));
        format!("smt({}).", names.join(" "))
    }

    /// A side goal (a condition, the side goal of `rcondt`): `auto => /#`, then the ladder,
    /// else an admit whose reason is `Router` for the router prelude and otherwise
    /// `domino-verified-ec-failed`: Domino decided this branch under its assumptions.
    fn close_side_goal(&mut self, node: usize, claim: &str, router: bool) -> R<()> {
        if self.try_close(&["auto => /#."])? || self.ladder()? {
            return Ok(());
        }
        if router {
            return self.admit(
                AdmitReason::Router,
                "router",
                claim,
                DominoView::NotApplicable,
            );
        }
        let id = self.id_below(node, &Part::Whole, DominoView::Verified);
        self.admit(
            AdmitReason::DominoVerifiedEcFailed,
            &id,
            claim,
            DominoView::Verified,
        )
    }

    // ------------------------------------------------------------------
    // The walk
    // ------------------------------------------------------------------

    /// Proves the front goal, which is the program goal of joint node `idx`.
    pub(super) fn prove_node(&mut self, idx: usize) -> R<()> {
        if let Some(live) = &self.live {
            let node = self.tree.node(idx);
            let mut ids: Vec<String> = self
                .tree
                .pairs_below(idx)
                .map(|p| p.id.clone())
                .collect();
            ids.extend(node.stuck.clone());
            live.node_entered(&format!("N{idx}"), node.kind.as_str(), ids, Some(idx));
        }
        let parent = self.node.replace(idx);
        let result = self.prove_node_inner(idx);
        self.node = parent;
        if result.is_ok() {
            self.checkpoint();
        }
        if let Some(live) = &self.live {
            live.node_left();
        }
        result
    }

    fn prove_node_inner(&mut self, idx: usize) -> R<()> {
        let tree = self.tree;
        let node = tree.node(idx);
        self.session
            .set_context(&format!("{} N{idx} {}", self.oracle, node.kind.as_str()));

        // §3.6: a claim that fails in Domino is not worth EasyCrypt's time
        if let Some(pair) = tree.pairs_below(idx).next() {
            let all_fail = tree.pairs_below(idx).all(|p| {
                pair_view(p, &Part::EqualOutput) == DominoView::Fails
                    && pair_view(p, &Part::Invariant) == DominoView::Fails
            });
            if all_fail {
                let id = pair.id.clone();
                return self.admit(
                    AdmitReason::DominoFails,
                    &id,
                    "equal-output+invariant",
                    DominoView::Fails,
                );
            }
        }

        // rung 0 (§3.3): most abort branches close in one step
        if node.kind != NodeKind::TerminalPair && self.rung0 {
            let rung0 = self.timeouts.rung0;
            self.note_rung("0: auto => /#");
            if self.with_timeout(rung0, |p| p.try_close(&["auto => /#."]))? {
                return Ok(());
            }
        }

        match node.kind {
            NodeKind::TerminalPair => self.leaf(idx),
            NodeKind::Stuck => {
                let stuck = node
                    .stuck
                    .as_deref()
                    .and_then(|id| tree.outcome.stuck.iter().find(|s| s.id == id));
                let (id, claim) = stuck.map_or_else(
                    || (format!("N{idx}"), "stuck".to_string()),
                    |s| (s.id.clone(), format!("stuck/{}", s.reason.as_str())),
                );
                let view = tree
                    .pairs_below(idx)
                    .map(|p| pair_view(p, &Part::Whole))
                    .fold(DominoView::Verified, DominoView::worst);
                self.admit(AdmitReason::Stuck, &id, &claim, view)
            }
            NodeKind::Unreachable => {
                if self.try_close(&["exfalso; smt()."])? {
                    return Ok(());
                }
                self.admit(
                    AdmitReason::DominoVerifiedEcFailed,
                    &format!("N{idx}"),
                    "unreachable",
                    DominoView::Verified,
                )
            }
            _ => {
                let snap = self.snap();
                if self.step_node(idx)? {
                    return Ok(());
                }
                self.rollback(snap)?;
                self.stats.fallbacks += 1;
                self.prove_blind(idx, 64)
            }
        }
    }

    /// `sp k l.` for the assignments at the head of the front goal's programs, `k`/`l` counted
    /// from EasyCrypt's JSON. `false` if the front goal is not a program goal or `sp` failed.
    fn sp_front(&mut self) -> R<bool> {
        let Some((k, l)) = self.front().and_then(goals::sp_counts) else {
            return Ok(false);
        };
        if k + l == 0 {
            return Ok(true);
        }
        self.send(&format!("sp {k} {l}."))
    }

    /// The tactic of a non-terminal, non-stuck node and its children. `Ok(false)` if the
    /// tactic did not apply (nothing of the children has been handled then).
    fn step_node(&mut self, idx: usize) -> R<bool> {
        if !self.sp_front()? {
            return Ok(false);
        }
        match self.tree.node(idx).kind {
            NodeKind::Determined => self.determined(idx),
            NodeKind::Synchronized => self.synchronized(idx),
            NodeKind::Split => self.split(idx),
            NodeKind::SamplingSynchronized => self.sampling(idx, true),
            NodeKind::SamplingIndependent => self.sampling(idx, false),
            _ => Ok(false),
        }
    }

    /// The route of a joint child into the tree.
    fn handle_child(&mut self, parent: usize, child: &JointChild) -> R<()> {
        match &child.outcome {
            ChildOutcome::Explored { node } => self.prove_node(*node),
            ChildOutcome::Pruned { .. } => {
                if self.try_close(&["exfalso; smt()."])? || self.try_close(&["auto => /#."])? {
                    return Ok(());
                }
                self.admit(
                    AdmitReason::DominoVerifiedEcFailed,
                    &format!("N{parent}"),
                    "pruned-combination",
                    DominoView::Verified,
                )
            }
            ChildOutcome::NotExplored => self.admit(
                AdmitReason::DominoInconclusive,
                &format!("N{parent}"),
                "not-explored",
                DominoView::Inconclusive,
            ),
        }
    }

    fn determined(&mut self, idx: usize) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let [child] = node.children.as_slice() else {
            return Ok(false);
        };
        // (side number, decision) of every side that moved alone
        let steps: Vec<(u8, &str)> = [(1u8, &child.left), (2u8, &child.right)]
            .into_iter()
            .filter_map(|(side, step)| step.as_ref().map(|s| (side, s.decision.as_str())))
            .collect();
        if steps.is_empty() {
            return Ok(false);
        }
        for &(side, decision) in &steps {
            let tactic = match decision {
                "then" => "rcondt",
                "else" => "rcondf",
                _ => return Ok(false),
            };
            let before = self.count();
            let closing = format!("{tactic}{{{side}}} ^if; 1: auto => /#.");
            if self.send(&closing)? {
                // the side goal closed in the same sentence: the main goal is in front
                if self.count() != before {
                    return Ok(false);
                }
                continue;
            }
            // the side goal did not close in one step: take it on its own
            let plain = format!("{tactic}{{{side}}} ^if.");
            if !self.send(&plain)? || self.count() != before + 1 {
                return Ok(false);
            }
            if !self
                .front()
                .is_some_and(|g| goals::is_ambient(g) || goals::is_skip_pair(g))
            {
                return Ok(false);
            }
            self.bullet(|p| p.close_side_goal(idx, "side-goal", false))?;
        }
        self.handle_child(idx, child)?;
        Ok(true)
    }

    fn synchronized(&mut self, idx: usize) -> R<bool> {
        let node = self.tree.node(idx);
        if node.children.len() != 2 {
            return Ok(false);
        }
        let before = self.count();
        if !self.send("if.")? {
            return Ok(false);
        }
        // the condition, then the two arms: told apart by kind
        let shape_ok = self.count() == before + 2 && {
            let g = self.session.goals();
            goals::is_ambient(&g[0]) && goals::is_program(&g[1]) && goals::is_program(&g[2])
        };
        if !shape_ok {
            return Ok(false);
        }
        self.bullet(|p| p.close_side_goal(idx, "branch-condition", false))?;
        for child in &node.children {
            self.bullet(|p| p.handle_child(idx, child))?;
        }
        Ok(true)
    }

    fn split(&mut self, idx: usize) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let both =
            node.left.head.kind == HeadKind::Branch && node.right.head.kind == HeadKind::Branch;
        let before = self.count();
        if both {
            if node.children.len() != 4 {
                return Ok(false);
            }
            if !self.send("if{1}.")? || !self.two_programs_in_front(before) {
                return Ok(false);
            }
            for a in 0..2 {
                self.bullet(|p| {
                    let here = p.count();
                    if !p.send("if{2}.")? || !p.two_programs_in_front(here) {
                        // an arm EasyCrypt would not split further
                        return p.admit_ec_failed(idx, &Part::Whole, "split");
                    }
                    for b in 0..2 {
                        p.bullet(|p| p.handle_child(idx, &node.children[a * 2 + b]))?;
                    }
                    Ok(())
                })?;
            }
            return Ok(true);
        }
        // one side splits, the other waits
        if node.children.len() != 2 {
            return Ok(false);
        }
        let side = match &node.children[0] {
            c if c.left.is_some() => 1,
            c if c.right.is_some() => 2,
            _ => return Ok(false),
        };
        if !self.send(&format!("if{{{side}}}."))? || !self.two_programs_in_front(before) {
            return Ok(false);
        }
        for child in &node.children {
            self.bullet(|p| p.handle_child(idx, child))?;
        }
        Ok(true)
    }

    /// After a tactic that turned one goal (count `before`) into two program goals.
    fn two_programs_in_front(&self, before: usize) -> bool {
        self.count() == before + 1 && {
            let g = self.session.goals();
            goals::is_program(&g[0]) && goals::is_program(&g[1])
        }
    }

    fn sampling(&mut self, idx: usize, synchronized: bool) -> R<bool> {
        let tree = self.tree;
        let node = tree.node(idx);
        let [child] = node.children.as_slice() else {
            return Ok(false);
        };
        let Some((left, right)) = self.front().and_then(goals::sides) else {
            return Ok(false);
        };
        let (kl, hl) = goals::head_after_assignments(&left.stmt);
        let (kr, hr) = goals::head_after_assignments(&right.stmt);
        let rnd = |h: Option<&crate::easycrypt::json::Instr>| {
            h.filter(|i| i.kind == "rnd")
                .and_then(|i| i.lvalue.as_ref())
                .map(|l| l.pp.clone())
        };
        let (x, y) = (rnd(hl), rnd(hr));
        let before = self.count();
        let sentences: Vec<String> = if synchronized {
            let (Some(x), Some(y)) = (x, y) else {
                return Ok(false);
            };
            if kl + kr > 0 {
                // `sp` left assignments before the sampling: `seq` would swallow them
                return self.seq_post_admit(idx).map(|()| true);
            }
            let post = format!("(#pre /\\ {x}{{1}} = {y}{{2}})");
            ["auto => />", "auto => /#", "auto"]
                .iter()
                .map(|close| format!("seq 1 1 : {post}; 1: {close}."))
                .collect()
        } else {
            let (n, m) = match (child.left.is_some(), child.right.is_some(), x, y) {
                (true, false, Some(_), _) => (1, 0),
                (false, true, _, Some(_)) => (0, 1),
                _ => return Ok(false),
            };
            ["auto => />", "auto => /#", "auto"]
                .iter()
                .map(|close| format!("seq {n} {m} : (#pre); 1: {close}."))
                .collect()
        };
        let mut applied = false;
        for sentence in &sentences {
            if self.attempt(&[sentence], |p| {
                p.count() == before && p.front().is_some_and(goals::is_program)
            })? {
                applied = true;
                break;
            }
        }
        if !applied {
            return Ok(false);
        }
        self.handle_child(idx, child)?;
        Ok(true)
    }

    fn seq_post_admit(&mut self, idx: usize) -> R<()> {
        let id = self.id_below(idx, &Part::Whole, DominoView::Verified);
        self.admit(AdmitReason::SeqPost, &id, "sampling", DominoView::Verified)
    }

    // ------------------------------------------------------------------
    // Leaves (§3.5)
    // ------------------------------------------------------------------

    fn leaf(&mut self, idx: usize) -> R<()> {
        let tree = self.tree;
        let pair = tree.pair_of_node.get(&idx).map(|&i| &tree.outcome.pairs[i]);
        self.leaf_of(idx, pair)
    }

    fn leaf_of(&mut self, node: usize, pair: Option<&PairRecord>) -> R<()> {
        let fails = |part: &Part| pair.is_some_and(|p| pair_view(p, part) == DominoView::Fails);
        // a claim that fails in Domino: split at once, so the parts that can hold still get tried
        if !fails(&Part::EqualOutput) && !fails(&Part::Invariant) {
            let with_hints = format!("auto => /> &1 &2 *; {}", self.hint_sentence());
            let fast = "auto => /> &1 &2 *; smt().";
            // the fast path; then again after `sp.`, which also finishes the router's tail
            // `if`; then with the project's hints
            let attempts: [Vec<&str>; 3] =
                [vec![fast], vec!["sp.", fast], vec![with_hints.as_str()]];
            for steps in &attempts {
                if self.try_close(steps)? {
                    return Ok(());
                }
            }
        }
        // Split by meaning, before `/>` reorders and substitutes: `sp.` also finishes the
        // router's tail `if`, then `skip` leaves `forall &1 &2, pre => post` with `post`
        // (`equal-output /\ inv …`) as the program wrote it. A tail that `sp` cannot decide is
        // handled by `auto.` instead, whose wp turns it into an `if` inside the formula.
        let before = self.count();
        let premise = "hpre";
        let reduced = self.attempt(&["sp.", &format!("skip => &1 &2 {premise}.")], |p| {
            p.count() == before && p.front().is_some_and(goals::is_ambient)
        })? || self
            .attempt(&["auto.", &format!("move => &1 &2 {premise}.")], |p| {
                p.count() == before && p.front().is_some_and(goals::is_ambient)
            })?;
        if !reduced {
            return self.admit_ec_failed(node, &Part::Whole, "equal-output+invariant");
        }
        self.unfold_premise(premise)?;
        self.deadline = Some(std::time::Instant::now() + self.leaf_budget);
        let result = self.solve_ambient(node, pair, Part::Whole);
        self.deadline = None;
        result
    }

    /// Takes the front ambient goal apart along the JSON of its formula: binders and premises
    /// are introduced, conjunctions split, `inv` and `Domino_<rel>` unfolded; what is left is
    /// closed by [`Self::atom`].
    fn solve_ambient(&mut self, node: usize, pair: Option<&PairRecord>, part: Part) -> R<()> {
        enum Step {
            /// The binders of a `forall`.
            Intro(String),
            /// The premise of an implication, named.
            Premise(String),
            Split,
            Unfold(String),
            Atom,
        }
        let mut part = part;
        for _ in 0..64 {
            if self
                .deadline
                .is_some_and(|d| std::time::Instant::now() >= d)
            {
                return self.admit_part(node, pair, &part, " (leaf time budget spent)");
            }
            let (step, now) = {
                let Some(goal) = self.front() else {
                    return Ok(());
                };
                let concl = &goal.concl;
                let mut now = part.clone();
                let step = if let Some((names, _)) = goals::as_forall(concl) {
                    Step::Intro(names.join(" "))
                } else if goals::as_implication(concl).is_some() {
                    Step::Premise(goals::fresh_name(goal, "hpre"))
                } else if goals::as_conjunction(concl).is_some() {
                    Step::Split
                } else if let Some(op) = goals::app_op_leaf(concl) {
                    if op == "inv" {
                        now = Part::Invariant;
                        Step::Unfold("inv".into())
                    } else if let Some(rel) = op.strip_prefix("Domino_") {
                        now = Part::Relation(rel.to_string());
                        Step::Unfold(op.to_string())
                    } else {
                        Step::Atom
                    }
                } else {
                    Step::Atom
                };
                (step, now)
            };
            part = now;

            // §3.6: a part that fails in Domino is admitted without spending EasyCrypt time
            if let Some(p) = pair {
                if !matches!(part, Part::Whole) && pair_view(p, &part) == DominoView::Fails {
                    return self.admit(
                        AdmitReason::DominoFails,
                        &p.id,
                        &part.claim_label(),
                        DominoView::Fails,
                    );
                }
            }

            match step {
                Step::Intro(names) => {
                    if !self.send(&format!("move => {names}."))? {
                        return self.atom(node, pair, &part);
                    }
                }
                Step::Premise(name) => {
                    if !self.send(&format!("move => {name}."))? {
                        return self.atom(node, pair, &part);
                    }
                    // let the solver see through the invariant in the premise just introduced
                    self.unfold_premise(&name)?;
                }
                Step::Unfold(op) => {
                    if !self.send(&format!("rewrite /{op}."))? {
                        return self.atom(node, pair, &part);
                    }
                }
                Step::Split => {
                    let before = self.count();
                    if !self.send("split.")? || self.count() != before + 1 {
                        return self.atom(node, pair, &part);
                    }
                    // the first conjunct is the postcondition's equal-output part unless it
                    // is `inv` or a relation, which the next round recognises
                    let first = if part == Part::Whole {
                        Part::EqualOutput
                    } else {
                        part.clone()
                    };
                    self.bullet(|p| p.solve_ambient(node, pair, first))?;
                    let second = part.clone();
                    return self.bullet(|p| p.solve_ambient(node, pair, second));
                }
                Step::Atom => return self.atom(node, pair, &part),
            }
        }
        self.atom(node, pair, &part)
    }

    /// The end of a part: `smt()`, a rewrite of table reads, `smt(<hints>)`, else an admit that
    /// keeps the unfoldings and introductions already made.
    fn atom(&mut self, node: usize, pair: Option<&PairRecord>, part: &Part) -> R<()> {
        let hints = self.hint_sentence();
        for steps in [
            vec!["smt()."],
            vec!["rewrite !get_set_neqE.", "smt()."],
            vec![hints.as_str()],
        ] {
            if self.try_close(&steps)? {
                return Ok(());
            }
        }
        self.admit_part(node, pair, part, "")
    }

    /// Admits the front goal as `part` of the pair's claims: the reason is what Domino itself
    /// concluded about the part.
    fn admit_part(
        &mut self,
        node: usize,
        pair: Option<&PairRecord>,
        part: &Part,
        note: &str,
    ) -> R<()> {
        let claim = format!("{}{note}", part.claim_label());
        match pair {
            Some(p) => {
                let view = pair_view(p, part);
                let reason = match view {
                    DominoView::Fails => AdmitReason::DominoFails,
                    DominoView::Verified => AdmitReason::DominoVerifiedEcFailed,
                    _ => AdmitReason::DominoInconclusive,
                };
                self.admit(reason, &p.id, &claim, view)
            }
            None => self.admit_ec_failed(node, part, &claim),
        }
    }

    // ------------------------------------------------------------------
    // One oracle (§3.2)
    // ------------------------------------------------------------------

    /// Proves the oracle's `equivF` goal, which is in front: `proc; inline.`, the router
    /// prelude by construction, then the joint tree from its root. `align` is given the goal
    /// after `proc; inline.` and returns the descriptions of the alignment's mismatches
    /// ([`Self::mismatches`]); with any, the oracle is proved by the fallback.
    pub(super) fn oracle(&mut self, align: impl FnOnce(&Goal) -> Vec<String>) -> R<()> {
        self.script.enter_bullet(self.count());
        if let Some(live) = &self.live {
            live.node_entered("router prelude", "router", vec![], None);
        }
        let result = self.oracle_inner(align);
        if let Some(live) = &self.live {
            live.node_left();
        }
        self.script.leave_bullet();
        result
    }

    fn oracle_inner(&mut self, align: impl FnOnce(&Goal) -> Vec<String>) -> R<()> {
        self.session
            .set_context(&format!("{} router prelude", self.oracle));
        if !self.send("proc; inline.")? {
            self.admit(
                AdmitReason::ProgramMismatch,
                "N0",
                "proc; inline.",
                DominoView::NotApplicable,
            )?;
            return Ok(());
        }
        self.mismatches = self.front().map(align).unwrap_or_default();
        // the router prelude, by construction: `sp`, `if`, then the condition, the guarded body
        // (where lockstep begins) and the case where both sides already aborted
        let after_inline = self.snap();
        let before = self.count();
        let prelude = self.sp_front()? && self.send("if.")? && self.count() == before + 2 && {
            let g = self.session.goals();
            goals::is_ambient(&g[0]) && goals::is_program(&g[1]) && goals::is_program(&g[2])
        };
        if !prelude {
            self.rollback(after_inline)?;
            self.stats.fallbacks += 1;
            return self.prove_blind(0, 64);
        }
        self.bullet(|p| p.close_side_goal(0, "router-condition", true))?;
        if self.mismatches.is_empty() {
            self.bullet(|p| p.prove_node(0))?;
        } else {
            self.stats.fallbacks += 1;
            self.bullet(|p| p.prove_blind(0, 64))?;
        }
        self.bullet(|p| {
            let rung0 = p.timeouts.rung0;
            if p.rung0 && p.with_timeout(rung0, |p| p.try_close(&["auto => /#."]))? {
                return Ok(());
            }
            p.close_side_goal(0, "both-aborted", true)
        })
    }

    // ------------------------------------------------------------------
    // The fallback (§3.4): the PDF's trial procedure, without the joint tree
    // ------------------------------------------------------------------

    /// Proves the front goal by trying, at each program head, what `BranchingAlgorithm.pdf`
    /// does: `rcondt`/`rcondf` on either side, `if`, `if{1}`/`if{2}`, `seq` at samplings.
    /// Each trial runs under `undo`. Ends in an admit with reason `program-mismatch`.
    fn prove_blind(&mut self, node: usize, budget: usize) -> R<()> {
        let admit_mismatch = |p: &mut Self| {
            let id = format!("N{node}");
            p.admit(
                AdmitReason::ProgramMismatch,
                &id,
                "program",
                DominoView::Inconclusive,
            )
        };
        if budget == 0 || !self.front().is_some_and(goals::is_program) {
            return admit_mismatch(self);
        }
        let rung0 = self.timeouts.rung0;
        if self.rung0 && self.with_timeout(rung0, |p| p.try_close(&["auto => /#."]))? {
            return Ok(());
        }
        if !self.sp_front()? {
            return admit_mismatch(self);
        }
        let Some((left, right)) = self.front().and_then(goals::sides) else {
            return admit_mismatch(self);
        };
        if left.stmt.is_empty() && right.stmt.is_empty() {
            return self.leaf_of(node, None);
        }
        let head = |s: &crate::easycrypt::json::Side| s.stmt.first().map(|i| i.kind.clone());
        let (hl, hr) = (head(left), head(right));
        let rnd_name = |s: &crate::easycrypt::json::Side| {
            s.stmt
                .first()
                .and_then(|i| i.lvalue.as_ref())
                .map(|l| l.pp.clone())
        };
        let (xl, xr) = (rnd_name(left), rnd_name(right));
        let before = self.count();

        // 1./2. a side whose condition is decided
        let mut trials: Vec<(String, u8)> = Vec::new(); // (sentence, kind of continuation)
        for (side, h) in [(1, &hl), (2, &hr)] {
            if h.as_deref() == Some("if") {
                for tactic in ["rcondt", "rcondf"] {
                    trials.push((format!("{tactic}{{{side}}} ^if; 1: auto => /#."), 0));
                }
            }
        }
        for (sentence, _) in &trials {
            if self.attempt(&[sentence], |p| p.count() == before)? {
                return self.prove_blind(node, budget - 1);
            }
        }
        // 3. `if`: condition, then, else
        if hl.as_deref() == Some("if") && hr.as_deref() == Some("if") {
            let snap = self.snap();
            if self.send("if.")?
                && self.count() == before + 2
                && goals::is_ambient(&self.session.goals()[0])
            {
                self.bullet(|p| p.close_side_goal(node, "branch-condition", false))?;
                self.bullet(|p| p.prove_blind(node, budget - 1))?;
                return self.bullet(|p| p.prove_blind(node, budget - 1));
            }
            self.rollback(snap)?;
        }
        // 4. `if{1}` / `if{2}`
        for (side, h) in [(1, &hl), (2, &hr)] {
            if h.as_deref() != Some("if") {
                continue;
            }
            let snap = self.snap();
            if self.send(&format!("if{{{side}}}."))? && self.two_programs_in_front(before) {
                self.bullet(|p| p.prove_blind(node, budget - 1))?;
                return self.bullet(|p| p.prove_blind(node, budget - 1));
            }
            self.rollback(snap)?;
        }
        // 5. samplings
        let seqs: Vec<String> = match (&xl, &xr, hl.as_deref(), hr.as_deref()) {
            (Some(x), Some(y), Some("rnd"), Some("rnd")) => {
                vec![format!(
                    "seq 1 1 : (#pre /\\ {x}{{1}} = {y}{{2}}); 1: auto => /#."
                )]
            }
            (Some(_), _, Some("rnd"), _) => vec!["seq 1 0 : (#pre); 1: auto => /#.".into()],
            (_, Some(_), _, Some("rnd")) => vec!["seq 0 1 : (#pre); 1: auto => /#.".into()],
            _ => vec![],
        };
        for sentence in &seqs {
            if self.attempt(&[sentence], |p| p.count() == before)? {
                return self.prove_blind(node, budget - 1);
            }
        }
        admit_mismatch(self)
    }
}
