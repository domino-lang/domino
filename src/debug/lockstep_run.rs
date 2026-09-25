// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino debug --easycrypt`: lockstep execution of one oracle of an
//! equivalence, on the EasyCrypt listing (story 23).
//!
//! [`run_lockstep_command`] sets up what the engine ([`crate::debug::lockstep`])
//! needs and writes the artifacts ([`crate::debug::lockstep_report`]):
//!
//! - The oracle is lowered from the `EasyCryptTransform` game instances
//!   ([`inline_oracle_ec`]) and **executed against the Domino
//!   (`DebugTransform`) game instances**, whose state places, sample ids and
//!   entry returns the claims are built from (story 08 §6).
//! - The solver's base frame is the sequential debugger's, with the claim
//!   assumptions of a claim with **no dependencies**: the invariant on the old
//!   states (main, per game, per package), the randomness-mapping condition,
//!   and `emit_auto_randomness`; the arguments are the same constants on both
//!   sides. No `no-abort`, no project lemma: EasyCrypt has neither.
//! - **Equal-output** is the conjunction of the `equal-aborts` and `same-output`
//!   goals. `same-output` alone already means something when a side aborts: it
//!   compares the two `ReturnValueOrAbort` values, and an aborting side's is the
//!   `abort` constructor, so a pair where exactly one side aborts fails it. The
//!   conjunction is kept so equal-output reads as the two claims it stands for.
//! - **Invariant** is the `invariant` claim's goal on the new states. Domino's
//!   abort return carries no game state (`smt_construct_abort` ignores it), so
//!   on a side that aborts the new state is unconstrained; EasyCrypt's `inv`
//!   instead guards the relations under `!abort_flag`. The two differ at pairs
//!   where a side aborts, and `prove` gets around it with the `no-abort`
//!   dependency this mode does not assume. `prove`'s semantics are unchanged.
//! - The per-relation sub-verdicts use the names of the `define-state-relation`s
//!   ([`EquivalenceContext::state_relation_names`]), the list the EasyCrypt
//!   `inv` operator conjoins (`writers::easycrypt::invariant`).

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::time::{Duration, Instant};

use serde_derive::Serialize;

use crate::debug::driver::{
    base_frame, equivalence_of, sites_view, DebugError, SiteView, StopReason, Verdict,
};
use crate::debug::exec::TerminalPath;
use crate::debug::ir::{count_terminals, inline_oracle, Label};
use crate::debug::lockstep::{
    run_lockstep, ChildOutcome, LockstepObserver, LockstepOptions, LockstepOutcome, LockstepSide,
    LockstepTerms, PairRecord, Pairing, RelationGoal, StuckPoint,
};
use crate::debug::lockstep_report::{self, LockstepSmtWriter};
use crate::debug::lockstep_viewer;
use crate::debug::progress::{DebugEvent, DebugObserver};
use crate::debug::render;
use crate::debug::smtout::SmtOut;
use crate::project::Project;
use crate::theorem::{Claim, ClaimType};
use crate::transforms::theorem_transforms::{
    DebugTransform, EasyCryptTransform, EquivalenceTransform,
};
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::{SmtSolver, SmtSolverBackend};
use crate::writers::easycrypt::lower::inline_oracle_ec;
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtExpr, SmtNot};

/// Schema version of a lockstep `trace.json`. Sequential traces keep
/// [`crate::debug::driver::TRACE_SCHEMA`].
pub const LOCKSTEP_TRACE_SCHEMA: u32 = 9;

/// The least time between two flushes of the partial artifacts while a run is
/// in progress: at most two a second (story 24). The page refreshes every two
/// seconds, and serialising a big trace is not free.
const FLUSH_GAP: Duration = Duration::from_millis(500);

/// Rate limit for the partial flushes.
struct FlushThrottle {
    gap: Duration,
    last: Instant,
}

impl FlushThrottle {
    fn new(gap: Duration, now: Instant) -> Self {
        Self { gap, last: now }
    }

    /// Whether a flush is due at `now`; if so, it counts as done.
    fn due(&mut self, now: Instant) -> bool {
        if now.saturating_duration_since(self.last) < self.gap {
            return false;
        }
        self.last = now;
        true
    }
}

/// The CLI knobs that have a meaning in lockstep mode.
#[derive(Debug, Clone, Copy)]
pub struct LockstepDebugOptions {
    /// Per-query solver timeout in milliseconds; a timeout counts as `unknown`.
    pub timeout_ms: Option<u64>,
    /// Stop after this many joint paths.
    pub max_paths: Option<usize>,
    pub smt_out: SmtOut,
    pub transcript: bool,
}

impl Default for LockstepDebugOptions {
    fn default() -> Self {
        Self {
            timeout_ms: None,
            max_paths: None,
            smt_out: SmtOut::Failures,
            transcript: false,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct LockstepOptionsView {
    pub timeout_ms: Option<u64>,
    pub max_paths: Option<usize>,
    pub smt: SmtOut,
    pub transcript: bool,
}

impl From<&LockstepDebugOptions> for LockstepOptionsView {
    fn from(o: &LockstepDebugOptions) -> Self {
        Self {
            timeout_ms: o.timeout_ms,
            max_paths: o.max_paths,
            smt: o.smt_out,
            transcript: o.transcript,
        }
    }
}

/// The negated goals the run asks about, rendered.
#[derive(Debug, Clone, Serialize)]
pub struct GoalsView {
    pub equal_output_smt: String,
    pub invariant_smt: String,
    pub relations: Vec<RelationGoalView>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RelationGoalView {
    pub name: String,
    pub smt: String,
}

/// What a lockstep run is about: its identity, options, goals and listings.
/// Everything here is known before the engine starts.
#[derive(Debug, Clone, Serialize)]
pub struct LockstepMeta {
    /// Always [`LOCKSTEP_TRACE_SCHEMA`].
    pub schema: u32,
    /// Always `lockstep`.
    pub mode: &'static str,
    /// The listing the engine walked: `easycrypt` on the command line.
    pub listing: &'static str,
    pub theorem: String,
    pub proofstep: usize,
    pub left_game: String,
    pub right_game: String,
    pub oracle: String,
    /// The output directory. Absolute — kept out of `trace.json` so two runs of
    /// an unchanged project produce identical bytes.
    #[serde(skip)]
    pub out_dir: String,
    pub options: LockstepOptionsView,
    /// The assumptions and definitions asserted once at solver level 0.
    pub base_frame_smt: String,
    pub goals: GoalsView,
    pub left_listing: String,
    pub right_listing: String,
    pub left_sites: BTreeMap<Label, SiteView>,
    pub right_sites: BTreeMap<Label, SiteView>,
    /// Syntactic terminal counts of the two lowered oracles: what a sequential
    /// run would pair up (left times right).
    pub left_syntactic: u64,
    pub right_syntactic: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct VerdictCounts {
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

impl VerdictCounts {
    pub(crate) fn bump(&mut self, v: &Verdict) {
        match v {
            Verdict::Verified => self.verified += 1,
            Verdict::Unreachable => self.unreachable += 1,
            Verdict::GoalFails { .. } => self.goal_fails += 1,
            Verdict::Inconclusive { .. } => self.inconclusive += 1,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct VerdictPairCount {
    pub equal_output: &'static str,
    pub invariant: &'static str,
    pub count: usize,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct LockstepSummary {
    pub joint_paths: usize,
    pub nodes: usize,
    /// Children of a split the solver proved infeasible.
    pub pruned_children: usize,
    pub node_kinds: BTreeMap<String, usize>,
    pub equal_output: VerdictCounts,
    pub invariant: VerdictCounts,
    /// Joint paths per `(equal-output, invariant)` verdict pair.
    pub verdict_pairs: Vec<VerdictPairCount>,
    /// Joint paths on which a state relation failed or was inconclusive, per
    /// relation.
    pub relation_failures: BTreeMap<String, usize>,
    pub stuck_points: usize,
}

/// A finished (or stopped) lockstep run.
#[derive(Debug, Clone)]
pub struct LockstepRun {
    pub meta: LockstepMeta,
    pub outcome: LockstepOutcome,
    pub summary: LockstepSummary,
    /// Wall-clock time; never serialised.
    pub elapsed: Duration,
}

impl LockstepRun {
    /// Every joint path is equal-output and invariant-preserving (or
    /// unreachable) and the tree was explored to the end. Stuck points do not
    /// count against it: they are places a proof needs a human, not failures.
    /// This is the process exit-code criterion.
    pub fn is_ok(&self) -> bool {
        self.outcome.stop_reason == StopReason::Completed
            && !self
                .outcome
                .pairs
                .iter()
                .any(|p| p.equal_output.is_failure() || p.invariant.is_failure())
    }
}

/// The counts of `outcome` so far.
pub fn summarize(outcome: &LockstepOutcome) -> LockstepSummary {
    let mut s = LockstepSummary {
        joint_paths: outcome.pairs.len(),
        nodes: outcome.tree.nodes.len(),
        stuck_points: outcome.stuck.len(),
        ..LockstepSummary::default()
    };
    for node in &outcome.tree.nodes {
        *s.node_kinds
            .entry(node.kind.as_str().to_string())
            .or_insert(0) += 1;
        s.pruned_children += node
            .children
            .iter()
            .filter(|c| matches!(c.outcome, ChildOutcome::Pruned { .. }))
            .count();
    }
    let mut pairs: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for p in &outcome.pairs {
        s.equal_output.bump(&p.equal_output);
        s.invariant.bump(&p.invariant);
        *pairs
            .entry((rank(&p.equal_output), rank(&p.invariant)))
            .or_insert(0) += 1;
        for r in &p.relations {
            if r.verdict.is_failure() {
                *s.relation_failures.entry(r.name.clone()).or_insert(0) += 1;
            }
        }
    }
    s.verdict_pairs = pairs
        .into_iter()
        .map(|((eo, inv), count)| VerdictPairCount {
            equal_output: RANKED[eo],
            invariant: RANKED[inv],
            count,
        })
        .collect();
    s
}

const RANKED: [&str; 4] = ["verified", "unreachable", "goal-fails", "inconclusive"];

fn rank(v: &Verdict) -> usize {
    match v {
        Verdict::Verified => 0,
        Verdict::Unreachable => 1,
        Verdict::GoalFails { .. } => 2,
        Verdict::Inconclusive { .. } => 3,
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

fn no_dependency_claim(name: &str, ty: ClaimType) -> Claim {
    Claim {
        name: name.to_string(),
        ty,
        dependencies: Vec::new(),
        admitted: false,
    }
}

/// The engine's solver vocabulary for `oracle`, from the equivalence context.
fn lockstep_terms(eqctx: &EquivalenceContext<'_>, oracle: &str) -> LockstepTerms {
    let goal_of = |name: &str| {
        eqctx
            .claim_assumptions_and_goal(&no_dependency_claim(name, ClaimType::Lemma), oracle)
            .1
    };
    let equal_output: SmtExpr =
        SmtAnd(vec![goal_of("equal-aborts"), goal_of("same-output")]).into();
    let negated_relation = |name: &str| {
        eqctx.emit_claim_goal_negated(&no_dependency_claim(name, ClaimType::Invariant), oracle)
    };

    LockstepTerms {
        equal_output_negated: SmtAssert(SmtNot(equal_output)).into(),
        invariant_negated: negated_relation("invariant"),
        relations: eqctx
            .state_relation_names()
            .into_iter()
            .map(|name| RelationGoal {
                negated: negated_relation(&name),
                name,
            })
            .collect(),
        pairings: eqctx
            .randomness_mapping_candidates(oracle)
            .iter()
            .map(|entry| Pairing {
                left_sample: entry.sample_left,
                right_sample: entry.sample_right,
                offset_left: entry.offset_left,
                offset_right: entry.offset_right,
                premise: eqctx.randomness_mapping_premise(oracle, entry),
            })
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// The command
// ---------------------------------------------------------------------------

/// Bridges the engine's callbacks to progress events, `smt/` files and the
/// periodic flush.
struct RunObserver<'a, 'o> {
    progress: &'a RefCell<&'o mut dyn DebugObserver>,
    meta: &'a LockstepMeta,
    out_dir: &'a Path,
    smt: &'a LockstepSmtWriter,
    goals: Vec<(String, String)>,
    throttle: FlushThrottle,
}

impl RunObserver<'_, '_> {
    /// Rewrite the artifacts of the run so far, as the live page (it
    /// refreshes itself), if the throttle allows.
    fn flush_if_due(&mut self, outcome: &LockstepOutcome) -> Result<(), DebugError> {
        if self.throttle.due(Instant::now()) {
            lockstep_report::flush(self.meta, outcome, &summarize(outcome), self.out_dir, true)?;
        }
        Ok(())
    }
}

impl LockstepObserver for RunObserver<'_, '_> {
    fn node_entered(&mut self, outcome: &LockstepOutcome, node: usize) -> Result<(), DebugError> {
        self.progress.borrow_mut().on_event(&DebugEvent::JointNode {
            index: node,
            kind: outcome.tree.nodes[node].kind.as_str(),
        });
        self.flush_if_due(outcome)
    }

    fn pair_checked(
        &mut self,
        outcome: &LockstepOutcome,
        pair: &PairRecord,
        left: &TerminalPath,
        right: &TerminalPath,
        elapsed: Duration,
    ) -> Result<(), DebugError> {
        self.smt.write_pair(pair, left, right, &self.goals)?;
        self.progress
            .borrow_mut()
            .on_event(&DebugEvent::JointPairChecked {
                id: &pair.id,
                equal_output: &pair.equal_output,
                invariant: &pair.invariant,
                elapsed,
            });
        self.flush_if_due(outcome)
    }

    fn stuck_found(&mut self, _outcome: &LockstepOutcome, stuck: &StuckPoint) {
        self.progress
            .borrow_mut()
            .on_event(&DebugEvent::StuckPointFound {
                id: &stuck.id,
                side: stuck.side,
                label: stuck.label,
                reason: stuck.reason.as_str(),
            });
    }
}

/// Drop the refresh tag from the page on disk, after a run that died without
/// its final write. Best effort: the run's own error is what gets reported.
fn settle_page(out_dir: &Path) {
    let path = out_dir.join("index.html");
    if let Ok(page) = std::fs::read_to_string(&path) {
        let _ = std::fs::write(&path, lockstep_viewer::without_refresh(&page));
    }
}

/// The code the engine walks. The command line only offers the EasyCrypt
/// listing; the Domino listing (`inline_oracle` on the `DebugTransform` game
/// instances) is what a follow-up on `amir/symbolic-execution-debugger` will
/// expose, and is what the engine's own tests run on, since the engine does not
/// care which it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ListingKind {
    EasyCrypt,
    #[allow(dead_code)] // built by the engine tests, which need `cvc5-lib`
    Domino,
}

impl ListingKind {
    fn as_str(self) -> &'static str {
        match self {
            ListingKind::EasyCrypt => "easycrypt",
            ListingKind::Domino => "domino",
        }
    }
}

/// Run `domino debug --easycrypt` for one oracle of the equivalence at
/// `req_proofstep` of `req_proof`, and write its artifacts under `out`
/// (default `_build/debug/<theorem>/<left>-<right>/<oracle>/easycrypt/`).
#[allow(clippy::too_many_arguments)]
pub fn run_lockstep_command<P, B>(
    project: &P,
    req_proof: &str,
    req_proofstep: usize,
    oracle: &str,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: Option<PathBuf>,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<LockstepRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    run_lockstep_on(
        ListingKind::EasyCrypt,
        project,
        req_proof,
        req_proofstep,
        oracle,
        opts,
        backend,
        out,
        observer,
        stop,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_lockstep_on<P, B>(
    listing: ListingKind,
    project: &P,
    req_proof: &str,
    req_proofstep: usize,
    oracle: &str,
    opts: &LockstepDebugOptions,
    backend: &B,
    out: Option<PathBuf>,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<LockstepRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();

    let theorem = project
        .get_theorem(req_proof)
        .ok_or_else(|| DebugError::TheoremNotFound {
            name: req_proof.to_string(),
        })?;
    let eq = equivalence_of(theorem, req_proofstep)?;

    // The same three transforms of the theorem as the sequential debugger, plus
    // the one `domino easycrypt` exports: the base frame comes from the
    // treeified pipeline, the executed game instances from `DebugTransform`, and
    // the listing lowered from `EasyCryptTransform`.
    let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(theorem)?;
    let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
    eqctx.load_invariants(project)?;

    let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(theorem)?;
    let left_inst = theorem_dbg
        .find_game_instance(eq.left_name())
        .expect("left game instance exists");
    let right_inst = theorem_dbg
        .find_game_instance(eq.right_name())
        .expect("right game instance exists");
    let sample_info_of = |name: &str| {
        &auxs_dbg
            .iter()
            .find(|(n, _)| n == name)
            .expect("aux for game instance")
            .1
            .sample_info
    };

    if !eqctx
        .left_game_inst_ctx()
        .game()
        .exports
        .iter()
        .any(|export| export.name() == oracle)
    {
        return Err(DebugError::OracleNotExported {
            oracle: oracle.to_string(),
            game_inst: eq.left_name().to_string(),
        });
    }

    let (left_inl, right_inl) = match listing {
        ListingKind::EasyCrypt => {
            let (theorem_ec, _) = EasyCryptTransform.transform_theorem(theorem)?;
            (
                inline_oracle_ec(
                    theorem_ec
                        .find_game_instance(eq.left_name())
                        .expect("left game instance exists"),
                    oracle,
                )?,
                inline_oracle_ec(
                    theorem_ec
                        .find_game_instance(eq.right_name())
                        .expect("right game instance exists"),
                    oracle,
                )?,
            )
        }
        ListingKind::Domino => (
            inline_oracle(left_inst, oracle)?,
            inline_oracle(right_inst, oracle)?,
        ),
    };

    observer.on_event(&DebugEvent::Started {
        oracle,
        claim: "equal-output, invariant",
        admitted: false,
    });

    let out_dir = out.unwrap_or_else(|| {
        let mut path = project.get_root_dir();
        path.push("_build/debug");
        path.push(eq.theorem_name());
        path.push(format!("{}-{}", eq.left_name(), eq.right_name()));
        path.push(oracle);
        path.push("easycrypt");
        path
    });
    std::fs::create_dir_all(out_dir.join("models"))?;

    // The assumptions: the base frame with a claim that has no dependencies.
    let assumptions_claim = no_dependency_claim("invariant", ClaimType::Invariant);
    let base = base_frame(&eqctx, oracle, &assumptions_claim);
    let base_frame_smt = base
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    let terms = lockstep_terms(&eqctx, oracle);
    let goals_view = GoalsView {
        equal_output_smt: terms.equal_output_negated.to_string(),
        invariant_smt: terms.invariant_negated.to_string(),
        relations: terms
            .relations
            .iter()
            .map(|r| RelationGoalView {
                name: r.name.clone(),
                smt: r.negated.to_string(),
            })
            .collect(),
    };
    // `(name, smt)` of every check, in the order the engine runs them.
    let mut goals = vec![
        (
            "equal-output".to_string(),
            goals_view.equal_output_smt.clone(),
        ),
        ("invariant".to_string(), goals_view.invariant_smt.clone()),
    ];
    goals.extend(
        goals_view
            .relations
            .iter()
            .map(|r| (format!("relation-{}", r.name), r.smt.clone())),
    );

    let meta = LockstepMeta {
        schema: LOCKSTEP_TRACE_SCHEMA,
        mode: "lockstep",
        listing: listing.as_str(),
        theorem: eq.theorem_name().to_string(),
        proofstep: req_proofstep,
        left_game: eq.left_name().to_string(),
        right_game: eq.right_name().to_string(),
        oracle: oracle.to_string(),
        out_dir: out_dir.display().to_string(),
        options: LockstepOptionsView::from(opts),
        base_frame_smt,
        goals: goals_view,
        left_listing: left_inl.listing.text.clone(),
        right_listing: right_inl.listing.text.clone(),
        left_sites: sites_view(&left_inl.listing),
        right_sites: sites_view(&right_inl.listing),
        left_syntactic: count_terminals(&left_inl),
        right_syntactic: count_terminals(&right_inl),
    };

    let smt_header = format!(
        "; domino debug --easycrypt — theorem {}, proofstep {}, {} == {}\n; oracle {}\n",
        meta.theorem, meta.proofstep, meta.left_game, meta.right_game, meta.oracle
    );
    let smt_writer =
        LockstepSmtWriter::new(&out_dir, opts.smt_out, smt_header, &meta.base_frame_smt)?;

    let mut solver = if opts.transcript {
        let transcript = std::fs::File::create(out_dir.join("transcript.smt2"))?;
        backend.new_smtsolver_with_transcript(transcript)?
    } else {
        backend.new_smtsolver()?
    };
    if let Some(ms) = opts.timeout_ms {
        solver.set_option("tlimit-per", &ms.to_string())?;
    }
    for entry in &base {
        solver.write_smt(entry.clone())?;
    }

    // An empty trace first, so the directory is complete even if the run dies.
    let empty = LockstepOutcome {
        tree: Default::default(),
        pairs: Vec::new(),
        stuck: Vec::new(),
        stop_reason: StopReason::Completed,
    };
    lockstep_report::flush(&meta, &empty, &summarize(&empty), &out_dir, true)?;

    let progress = RefCell::new(observer);
    let engine_opts = LockstepOptions {
        max_paths: opts.max_paths,
        stop,
        out_dir: &out_dir,
    };
    let mut run_observer = RunObserver {
        progress: &progress,
        meta: &meta,
        out_dir: &out_dir,
        smt: &smt_writer,
        goals,
        throttle: FlushThrottle::new(FLUSH_GAP, Instant::now()),
    };
    let outcome = run_lockstep(
        &mut solver,
        LockstepSide {
            inlined: &left_inl,
            game_inst: left_inst,
            sample_info: sample_info_of(eq.left_name()),
        },
        LockstepSide {
            inlined: &right_inl,
            game_inst: right_inst,
            sample_info: sample_info_of(eq.right_name()),
        },
        &terms,
        &engine_opts,
        &mut run_observer,
    );
    solver.close();
    let outcome = match outcome {
        Ok(outcome) => outcome,
        Err(e) => {
            // The run ended without a final write: the page must not keep
            // refreshing forever.
            settle_page(&out_dir);
            return Err(e);
        }
    };

    let summary = summarize(&outcome);
    let finish = || -> std::io::Result<()> {
        std::fs::write(
            out_dir.join("inlined.txt"),
            render::side_by_side(&meta.left_listing, &meta.right_listing),
        )?;
        lockstep_report::flush(&meta, &outcome, &summary, &out_dir, false)
    };
    if let Err(e) = finish() {
        settle_page(&out_dir);
        return Err(e.into());
    }

    progress
        .borrow_mut()
        .on_event(&DebugEvent::LockstepFinished {
            pairs: outcome.pairs.len(),
            stuck: outcome.stuck.len(),
            stop_reason: outcome.stop_reason,
        });

    Ok(LockstepRun {
        meta,
        outcome,
        summary,
        elapsed: started.elapsed(),
    })
}

#[cfg(all(test, feature = "cvc5-lib"))]
mod tests {
    use super::*;
    use crate::debug::ir::inline_oracle;
    use crate::debug::lockstep::{ChildOutcome, NodeKind, StuckReason};
    use crate::debug::progress::NopObserver;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;

    /// One oracle of `testdata/lockstep/rules`, whose two sides are built so that
    /// each rule of the story's §3.3 fires on its own oracle. The engine runs on
    /// the Domino listing: it is listing-agnostic, and that listing has no
    /// plumbing branches to get in the way of exact node sequences.
    fn run_rules(oracle: &str) -> LockstepRun {
        run_rules_with(oracle, LockstepDebugOptions::default(), None)
    }

    fn run_rules_with(
        oracle: &str,
        opts: LockstepDebugOptions,
        out: Option<PathBuf>,
    ) -> LockstepRun {
        let dir = "testdata/lockstep/rules";
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let out = out.unwrap_or_else(|| tempfile::tempdir().unwrap().into_path());
        run_lockstep_on(
            ListingKind::Domino,
            &project,
            "T",
            0,
            oracle,
            &opts,
            &Cvc5LibBackend::new(true, opts.timeout_ms),
            Some(out),
            &mut NopObserver,
            None,
        )
        .unwrap()
    }

    fn kinds(run: &LockstepRun) -> Vec<NodeKind> {
        run.outcome.tree.nodes.iter().map(|n| n.kind).collect()
    }

    fn verdicts(run: &LockstepRun) -> Vec<(&'static str, &'static str)> {
        run.outcome
            .pairs
            .iter()
            .map(|p| (RANKED[rank(&p.equal_output)], RANKED[rank(&p.invariant)]))
            .collect()
    }

    #[test]
    fn a_condition_the_path_decides_is_a_determined_branch() {
        let run = run_rules("Determined");
        assert_eq!(
            kinds(&run),
            [
                NodeKind::Synchronized, // both asserts test `x >= 0`
                NodeKind::Determined,   // `x < 0` cannot hold once the assert held
                NodeKind::TerminalPair,
                NodeKind::TerminalPair, // both aborted
            ]
        );
        let node = &run.outcome.tree.nodes[1];
        assert_eq!(node.children.len(), 1);
        assert_eq!(node.children[0].left.as_ref().unwrap().decision, "else");
        assert!(node.children[0].right.is_none(), "the right side waited");
    }

    #[test]
    fn equivalent_conditions_are_a_synchronized_branch() {
        let run = run_rules("Synced");
        assert_eq!(
            kinds(&run),
            [
                NodeKind::Synchronized,
                NodeKind::TerminalPair,
                NodeKind::TerminalPair
            ]
        );
        // two children: both take then, both take else
        let root = &run.outcome.tree.nodes[0];
        let steps: Vec<_> = root
            .children
            .iter()
            .map(|c| {
                (
                    c.left.as_ref().unwrap().decision.clone(),
                    c.right.as_ref().unwrap().decision.clone(),
                )
            })
            .collect();
        assert_eq!(
            steps,
            [
                ("then".into(), "then".into()),
                ("else".into(), "else".into())
            ]
        );
        assert_eq!(verdicts(&run), [("verified", "verified"); 2]);
    }

    #[test]
    fn unrelated_conditions_split_into_every_combination() {
        let run = run_rules("Split");
        assert_eq!(kinds(&run)[0], NodeKind::Split);
        assert_eq!(run.outcome.tree.nodes[0].children.len(), 4);
        assert_eq!(run.summary.pruned_children, 0);
        // (then,then) and (else,else) agree; the mixed ones return 1 against 2
        assert_eq!(
            verdicts(&run),
            [
                ("verified", "verified"),
                ("goal-fails", "verified"),
                ("goal-fails", "verified"),
                ("verified", "verified"),
            ]
        );
        assert!(!run.is_ok());
    }

    #[test]
    fn a_split_prunes_the_combinations_the_solver_proves_infeasible() {
        let run = run_rules("SplitPruned");
        let root = &run.outcome.tree.nodes[0];
        assert_eq!(root.kind, NodeKind::Split);
        let pruned: Vec<bool> = root
            .children
            .iter()
            .map(|c| matches!(c.outcome, ChildOutcome::Pruned { .. }))
            .collect();
        // (b, not b) and (not b, b) are the only feasible ones
        assert_eq!(pruned, [true, false, false, true]);
        assert_eq!(run.outcome.pairs.len(), 2);
        assert_eq!(verdicts(&run), [("verified", "verified"); 2]);
    }

    #[test]
    fn a_branch_on_one_side_splits_that_side_alone() {
        let run = run_rules("OneSided");
        assert_eq!(
            kinds(&run),
            [
                NodeKind::Split,
                NodeKind::TerminalPair,
                NodeKind::TerminalPair
            ]
        );
        for child in &run.outcome.tree.nodes[0].children {
            assert!(child.left.is_some() && child.right.is_none());
        }
    }

    #[test]
    fn samplings_the_mapping_forces_equal_are_synchronized() {
        let run = run_rules("SyncSample");
        assert_eq!(
            kinds(&run),
            [NodeKind::SamplingSynchronized, NodeKind::TerminalPair]
        );
        assert_eq!(verdicts(&run), [("verified", "verified")]);
        assert!(run.outcome.stuck.is_empty());
    }

    #[test]
    fn a_sampling_the_mapping_relates_to_nothing_is_independent() {
        let run = run_rules("IndepSample");
        assert_eq!(
            kinds(&run),
            [
                NodeKind::SamplingIndependent,
                NodeKind::SamplingSynchronized,
                NodeKind::TerminalPair
            ]
        );
        assert!(run.outcome.tree.nodes[0].children[0].right.is_none());
        assert!(run.outcome.stuck.is_empty());
    }

    #[test]
    fn a_mapping_that_depends_on_an_argument_is_a_stuck_point() {
        let run = run_rules("StuckArg");
        assert_eq!(
            kinds(&run),
            [NodeKind::Stuck, NodeKind::Stuck, NodeKind::TerminalPair]
        );
        // the pairing holds only for x > 0, so neither draw can be handed to
        // EasyCrypt as paired: left first, then right
        let stuck: Vec<_> = run
            .outcome
            .stuck
            .iter()
            .map(|s| (s.id.as_str(), s.side, s.reason))
            .collect();
        assert_eq!(
            stuck,
            [
                ("S1", "left", StuckReason::PairingSatNotValid),
                ("S2", "right", StuckReason::PairingSatNotValid),
            ]
        );
        // the execution went on with Domino's semantics, so the path still got
        // a verdict: the draws are equal only for x > 0
        assert_eq!(verdicts(&run)[0].0, "goal-fails");
    }

    #[test]
    fn samplings_in_opposite_orders_are_stuck_with_the_reasons_of_their_places() {
        let run = run_rules("StuckOrder");
        let stuck: Vec<_> = run
            .outcome
            .stuck
            .iter()
            .map(|s| (s.id.as_str(), s.side, s.reason))
            .collect();
        assert_eq!(
            stuck,
            [
                // left draws s1 first; its partner is right's second draw
                ("S1", "left", StuckReason::PartnerNotAtHead),
                // right's s1 comes when left has ended
                ("S2", "right", StuckReason::NoPartnerReachable),
            ]
        );
        assert_eq!(
            kinds(&run),
            [
                NodeKind::Stuck,
                NodeKind::SamplingSynchronized,
                NodeKind::Stuck,
                NodeKind::TerminalPair
            ]
        );
    }

    #[test]
    fn both_sides_are_checked_for_equal_output_at_a_terminal_pair() {
        let run = run_rules("BadOutput");
        assert_eq!(verdicts(&run), [("goal-fails", "verified")]);
        let model = match &run.outcome.pairs[0].equal_output {
            Verdict::GoalFails { model } => model.clone(),
            other => panic!("expected a failure, got {other:?}"),
        };
        assert_eq!(model, "models/J1.equal-output.smt2");
    }

    #[test]
    fn a_failing_invariant_is_broken_down_by_state_relation() {
        let run = run_rules("BadState");
        assert_eq!(verdicts(&run), [("verified", "goal-fails")]);
        let relations: Vec<_> = run.outcome.pairs[0]
            .relations
            .iter()
            .map(|r| (r.name.as_str(), rank(&r.verdict)))
            .collect();
        assert_eq!(relations, [("invariant", 2)]);
        assert_eq!(run.summary.relation_failures["invariant"], 1);
    }

    #[test]
    fn a_relation_breakdown_is_only_made_for_a_failing_invariant() {
        let run = run_rules("Synced");
        assert!(run.outcome.pairs.iter().all(|p| p.relations.is_empty()));
    }

    #[test]
    fn equal_output_fails_when_exactly_one_side_aborts() {
        let run = run_rules("AbortDiff");
        // the left assert holds: both return 1; it fails: left aborts, right returns
        let by_abort: Vec<_> = run
            .outcome
            .pairs
            .iter()
            .map(|p| {
                (
                    p.left.terminal.is_abort,
                    p.right.terminal.is_abort,
                    rank(&p.equal_output),
                )
            })
            .collect();
        assert_eq!(by_abort, [(false, false, 0), (true, false, 2)]);
    }

    #[test]
    fn equal_output_holds_when_both_sides_abort() {
        let run = run_rules("AbortBoth");
        let by_abort: Vec<_> = run
            .outcome
            .pairs
            .iter()
            .map(|p| {
                (
                    p.left.terminal.is_abort,
                    p.right.terminal.is_abort,
                    rank(&p.equal_output),
                )
            })
            .collect();
        assert_eq!(by_abort, [(false, false, 0), (true, true, 0)]);
    }

    #[test]
    fn the_invariant_is_checked_on_the_state_at_the_abort() {
        // Domino's abort return carries the state the side had reached, so the
        // `invariant` claim compares those states. EasyCrypt's `inv` guards its
        // relations under `!abort_flag` and would not ask this of the pair. The
        // engine reports Domino's answer; the difference is in the story-23
        // report.
        let run = run_rules("AbortState");
        let by_abort: Vec<_> = run
            .outcome
            .pairs
            .iter()
            .map(|p| {
                (
                    p.left.terminal.is_abort,
                    p.right.terminal.is_abort,
                    rank(&p.equal_output),
                    rank(&p.invariant),
                )
            })
            .collect();
        assert_eq!(by_abort, [(false, false, 0, 2), (true, true, 0, 2)]);
    }

    #[test]
    fn two_runs_give_identical_traces_and_ids() {
        for oracle in ["Split", "StuckOrder", "SplitPruned"] {
            let a = tempfile::tempdir().unwrap();
            let b = tempfile::tempdir().unwrap();
            run_rules_with(
                oracle,
                LockstepDebugOptions::default(),
                Some(a.path().to_path_buf()),
            );
            run_rules_with(
                oracle,
                LockstepDebugOptions::default(),
                Some(b.path().to_path_buf()),
            );
            for file in ["trace.json", "summary.txt", "index.html"] {
                assert_eq!(
                    std::fs::read_to_string(a.path().join(file)).unwrap(),
                    std::fs::read_to_string(b.path().join(file)).unwrap(),
                    "{oracle}: {file} differs between two runs"
                );
            }
        }
    }

    #[test]
    fn ids_follow_depth_first_order() {
        let run = run_rules("Split");
        let ids: Vec<_> = run.outcome.pairs.iter().map(|p| p.id.as_str()).collect();
        assert_eq!(ids, ["J1", "J2", "J3", "J4"]);
        // a pair's node is the terminal-pair node carrying its id, in pre-order
        let nodes: Vec<usize> = run.outcome.pairs.iter().map(|p| p.node).collect();
        assert!(nodes.windows(2).all(|w| w[0] < w[1]));
        for pair in &run.outcome.pairs {
            let node = &run.outcome.tree.nodes[pair.node];
            assert_eq!(node.pair.as_deref(), Some(pair.id.as_str()));
        }
    }

    #[test]
    fn max_paths_counts_joint_paths() {
        let run = run_rules_with(
            "Split",
            LockstepDebugOptions {
                max_paths: Some(2),
                ..LockstepDebugOptions::default()
            },
            None,
        );
        assert_eq!(run.outcome.pairs.len(), 2);
        assert_eq!(run.outcome.stop_reason, StopReason::MaxPaths { limit: 2 });
        assert!(!run.is_ok());
        // what the run did not reach stays visible in the tree
        assert!(run.outcome.tree.nodes[0]
            .children
            .iter()
            .any(|c| matches!(c.outcome, ChildOutcome::NotExplored)));
    }

    #[test]
    fn a_stop_request_ends_the_run_at_the_next_node() {
        let dir = "testdata/lockstep/rules";
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let stop = AtomicBool::new(true);
        let run = run_lockstep_on(
            ListingKind::Domino,
            &project,
            "T",
            0,
            "Split",
            &LockstepDebugOptions::default(),
            &Cvc5LibBackend::new(true, None),
            Some(tempfile::tempdir().unwrap().into_path()),
            &mut NopObserver,
            Some(&stop),
        )
        .unwrap();
        assert_eq!(run.outcome.stop_reason, StopReason::Interrupted);
        assert!(run.outcome.pairs.is_empty());
    }

    /// Records the calls the engine makes to a `LockstepObserver`.
    #[derive(Default)]
    struct Recorder {
        entered: Vec<usize>,
        left: Vec<usize>,
        children: Vec<(usize, usize)>,
        pairs: Vec<String>,
        stuck: Vec<String>,
    }

    impl LockstepObserver for Recorder {
        fn node_entered(&mut self, _: &LockstepOutcome, node: usize) -> Result<(), DebugError> {
            self.entered.push(node);
            Ok(())
        }
        fn child_entered(
            &mut self,
            _: &LockstepOutcome,
            node: usize,
            child: usize,
        ) -> Result<(), DebugError> {
            self.children.push((node, child));
            Ok(())
        }
        fn pair_checked(
            &mut self,
            _: &LockstepOutcome,
            pair: &PairRecord,
            _: &TerminalPath,
            _: &TerminalPath,
            _: Duration,
        ) -> Result<(), DebugError> {
            self.pairs.push(pair.id.clone());
            Ok(())
        }
        fn stuck_found(&mut self, _: &LockstepOutcome, stuck: &StuckPoint) {
            self.stuck.push(stuck.id.clone());
        }
        fn node_left(&mut self, _: &LockstepOutcome, node: usize) {
            self.left.push(node);
        }
    }

    #[test]
    fn the_observer_walks_the_joint_tree_depth_first() {
        // what story 27 drives: every node entered once, in pre-order, every
        // child announced before its subtree, every node left after it
        let dir = "testdata/lockstep/rules";
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let out = tempfile::tempdir().unwrap();

        // drive the engine directly, the way the command does
        let theorem = project.get_theorem("T").unwrap();
        let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        let eq = equivalence_of(theorem, 0).unwrap();
        let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
        eqctx.load_invariants(&project).unwrap();
        let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(theorem).unwrap();
        let left_inst = theorem_dbg.find_game_instance("gl").unwrap();
        let right_inst = theorem_dbg.find_game_instance("gr").unwrap();
        let si = |name: &str| {
            &auxs_dbg
                .iter()
                .find(|(n, _)| n == name)
                .unwrap()
                .1
                .sample_info
        };
        let left_inl = inline_oracle(left_inst, "StuckOrder").unwrap();
        let right_inl = inline_oracle(right_inst, "StuckOrder").unwrap();
        let base = base_frame(
            &eqctx,
            "StuckOrder",
            &no_dependency_claim("invariant", ClaimType::Invariant),
        );
        let terms = lockstep_terms(&eqctx, "StuckOrder");
        let mut solver = Cvc5LibBackend::new(true, None).new_smtsolver().unwrap();
        for e in &base {
            solver.write_smt(e.clone()).unwrap();
        }
        let mut recorder = Recorder::default();
        let outcome = run_lockstep(
            &mut solver,
            LockstepSide {
                inlined: &left_inl,
                game_inst: left_inst,
                sample_info: si("gl"),
            },
            LockstepSide {
                inlined: &right_inl,
                game_inst: right_inst,
                sample_info: si("gr"),
            },
            &terms,
            &LockstepOptions {
                max_paths: None,
                stop: None,
                out_dir: out.path(),
            },
            &mut recorder,
        )
        .unwrap();

        let all: Vec<usize> = (0..outcome.tree.nodes.len()).collect();
        assert_eq!(recorder.entered, all, "pre-order");
        let mut left = recorder.left.clone();
        left.sort_unstable();
        assert_eq!(left, all, "every node is left once");
        assert_eq!(recorder.pairs, ["J1"]);
        assert_eq!(recorder.stuck, ["S1", "S2"]);
        // a child is announced before the node it leads to is entered
        for &(parent, child) in &recorder.children {
            let ChildOutcome::Explored { node } =
                outcome.tree.nodes[parent].children[child].outcome
            else {
                panic!("an announced child is explored");
            };
            assert!(node > parent);
        }
    }

    // -- the real projects, on the EasyCrypt listing ----------------------------

    const HELLO: &str = "example-projects/hello-world";
    const KEM_DEM: &str = "example-projects/kem-dem/kem-dem-cca-ssp";

    /// `(project, theorem, oracle)` of the three acceptance cases.
    const CASES: [(&str, &str, &str); 3] = [
        (KEM_DEM, "kem_dem_cca_ssp", "PKENC"),
        (KEM_DEM, "kem_dem_cca_ssp", "PKDEC"),
        (HELLO, "Proof", "UsefulOracle"),
    ];

    fn lockstep_easycrypt(dir: &str, theorem: &str, oracle: &str) -> LockstepRun {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        run_lockstep_command(
            &project,
            theorem,
            0,
            oracle,
            &LockstepDebugOptions::default(),
            &Cvc5LibBackend::new(true, None),
            Some(tempfile::tempdir().unwrap().into_path()),
            &mut NopObserver,
            None,
        )
        .unwrap()
    }

    #[test]
    fn the_acceptance_cases_complete_and_write_their_artifacts() {
        for (dir, theorem, oracle) in CASES {
            let run = lockstep_easycrypt(dir, theorem, oracle);
            assert_eq!(run.outcome.stop_reason, StopReason::Completed, "{oracle}");
            assert!(!run.outcome.pairs.is_empty(), "{oracle}");
            assert_eq!(run.meta.listing, "easycrypt");
            let out = Path::new(&run.meta.out_dir);
            for file in [
                "trace.json",
                "summary.txt",
                "index.html",
                "inlined.txt",
                "smt/base.smt2",
            ] {
                assert!(out.join(file).is_file(), "{oracle}: {file} was not written");
            }
            let trace: serde_json::Value =
                serde_json::from_str(&std::fs::read_to_string(out.join("trace.json")).unwrap())
                    .unwrap();
            assert_eq!(trace["schema"], 9);
            assert_eq!(trace["mode"], "lockstep");
            assert_eq!(trace["listing"], "easycrypt");
        }
    }

    #[test]
    fn every_plumbing_branch_is_a_determined_node() {
        let mut plumbing_seen = 0;
        for (dir, theorem, oracle) in CASES {
            let run = lockstep_easycrypt(dir, theorem, oracle);
            for node in &run.outcome.tree.nodes {
                for side in [&node.left, &node.right] {
                    if side.plumbing.is_some() {
                        plumbing_seen += 1;
                        assert_eq!(
                            node.kind,
                            NodeKind::Determined,
                            "{oracle}: node {} stands at a plumbing branch",
                            node.index
                        );
                    }
                }
            }
        }
        assert!(plumbing_seen > 0, "the cases have plumbing branches");
    }

    #[test]
    fn a_done_guard_takes_its_then_side_alone() {
        let run = lockstep_easycrypt(KEM_DEM, "kem_dem_cca_ssp", "PKENC");
        let guards: Vec<_> = run
            .outcome
            .tree
            .nodes
            .iter()
            .filter(|n| {
                [&n.left, &n.right]
                    .iter()
                    .any(|s| s.plumbing == Some(crate::debug::lockstep::PlumbingKind::DoneGuard))
            })
            .collect();
        assert!(!guards.is_empty());
        for node in guards {
            assert_eq!(node.children.len(), 1, "a determined branch has one child");
            let step = node.children[0]
                .left
                .as_ref()
                .or(node.children[0].right.as_ref())
                .unwrap();
            assert_eq!(step.decision, "then");
        }
    }

    #[test]
    fn two_runs_on_a_real_project_give_identical_traces() {
        let a = lockstep_easycrypt(KEM_DEM, "kem_dem_cca_ssp", "PKENC");
        let b = lockstep_easycrypt(KEM_DEM, "kem_dem_cca_ssp", "PKENC");
        for file in ["trace.json", "index.html"] {
            assert_eq!(
                std::fs::read_to_string(Path::new(&a.meta.out_dir).join(file)).unwrap(),
                std::fs::read_to_string(Path::new(&b.meta.out_dir).join(file)).unwrap(),
                "{file}"
            );
        }
    }

    // -- the viewer page (story 24) ---------------------------------------------

    /// The JSON of the `<script type="application/json" id=…>` block of a page.
    fn embedded(page: &str, id: &str) -> serde_json::Value {
        let open = format!("<script type=\"application/json\" id=\"{id}\">");
        let start = page.find(&open).expect("block present") + open.len();
        let end = start + page[start..].find("</script>").unwrap();
        serde_json::from_str(&page[start..end]).unwrap()
    }

    /// Verdict-slug counts of the joint paths below `node`, computed from the
    /// raw `trace.json` with a walk that shares nothing with the viewer's.
    fn below(trace: &serde_json::Value, node: u64) -> Vec<&serde_json::Value> {
        let nodes = trace["tree"]["nodes"].as_array().unwrap();
        // Parent of every explored node.
        let mut parent = std::collections::HashMap::new();
        for n in nodes {
            for c in n["children"].as_array().unwrap() {
                if let Some(child) = c["outcome"]["node"].as_u64() {
                    parent.insert(child, n["index"].as_u64().unwrap());
                }
            }
        }
        trace["pairs"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|p| {
                let mut at = p["node"].as_u64().unwrap();
                loop {
                    if at == node {
                        return true;
                    }
                    match parent.get(&at) {
                        Some(up) => at = *up,
                        None => return false,
                    }
                }
            })
            .collect()
    }

    #[test]
    fn each_stuck_points_rollup_matches_a_count_taken_from_trace_json() {
        let mut checked = 0;
        for oracle in ["StuckArg", "StuckOrder", "BadState", "Split"] {
            let out = tempfile::tempdir().unwrap();
            run_rules_with(oracle, LockstepDebugOptions::default(), Some(out.path().to_path_buf()));
            let trace: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out.path().join("trace.json")).unwrap(),
            )
            .unwrap();
            let page = std::fs::read_to_string(out.path().join("index.html")).unwrap();
            let rollups = embedded(&page, "rollups");
            let rollups = rollups.as_array().unwrap();
            assert_eq!(rollups.len(), trace["stuck"].as_array().unwrap().len(), "{oracle}");
            for (stuck, rollup) in trace["stuck"].as_array().unwrap().iter().zip(rollups) {
                let pairs = below(&trace, stuck["node"].as_u64().unwrap());
                assert_eq!(rollup["id"], stuck["id"], "{oracle}");
                assert_eq!(rollup["pairs"].as_u64().unwrap() as usize, pairs.len(), "{oracle}");
                for claim in ["equal_output", "invariant"] {
                    let count = |slug: &str| {
                        pairs.iter().filter(|p| p[claim]["kind"] == slug).count() as u64
                    };
                    for (field, slug) in [
                        ("verified", "verified"),
                        ("unreachable", "unreachable"),
                        ("goal_fails", "goal-fails"),
                        ("inconclusive", "inconclusive"),
                    ] {
                        assert_eq!(
                            rollup[claim][field].as_u64().unwrap(),
                            count(slug),
                            "{oracle} {} {claim} {field}",
                            stuck["id"]
                        );
                    }
                }
                let failing_relations: usize = pairs
                    .iter()
                    .flat_map(|p| p["relations"].as_array().unwrap())
                    .filter(|r| matches!(r["verdict"]["kind"].as_str(), Some("goal-fails" | "inconclusive")))
                    .count();
                let rolled: usize = rollup["relations"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|r| r["failing"].as_array().unwrap().len())
                    .sum();
                assert_eq!(rolled, failing_relations, "{oracle}");
                checked += 1;
            }
        }
        assert!(checked >= 2, "the stuck oracles must have been exercised");
    }

    #[test]
    fn a_finished_page_does_not_refresh_and_a_live_one_does() {
        let run = lockstep_easycrypt(HELLO, "Proof", "UsefulOracle");
        let out = Path::new(&run.meta.out_dir);
        let page = std::fs::read_to_string(out.join("index.html")).unwrap();
        assert!(!page.contains("<meta http-equiv"), "the final page has no refresh tag");
        lockstep_report::flush(&run.meta, &run.outcome, &run.summary, out, true).unwrap();
        let live = std::fs::read_to_string(out.join("index.html")).unwrap();
        assert!(live.contains("<meta http-equiv=\"refresh\" content=\"2\">"));
        settle_page(out);
        assert_eq!(std::fs::read_to_string(out.join("index.html")).unwrap(), page);
    }

    #[test]
    fn the_viewer_page_embeds_the_trace_and_needs_no_network() {
        let run = lockstep_easycrypt(HELLO, "Proof", "UsefulOracle");
        let out = Path::new(&run.meta.out_dir);
        let page = std::fs::read_to_string(out.join("index.html")).unwrap();
        let trace: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(out.join("trace.json")).unwrap()).unwrap();
        assert_eq!(embedded(&page, "trace"), trace);
        for needle in ["http://", "https://", "fetch(", "XMLHttpRequest", "localStorage"] {
            assert!(!page.contains(needle), "{needle}");
        }
    }

    // -- one-directional consistency with the sequential debugger ---------------

    /// Sequential `domino debug` of `claim` on the Domino listing, and the claim's
    /// dependencies.
    fn sequential(
        dir: &str,
        theorem: &str,
        oracle: &str,
        claim: &str,
    ) -> (crate::debug::driver::DebugRun, usize) {
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let deps = {
            let th = project.get_theorem(theorem).unwrap();
            let eq = equivalence_of(th, 0).unwrap();
            eq.proof_tree_by_oracle_name(oracle)
                .iter()
                .find(|c| c.name() == claim)
                .map(|c| c.dependencies().len())
                .expect("the claim is in the proof tree")
        };
        let run = crate::debug::driver::run_debug_command(
            &project,
            theorem,
            0,
            oracle,
            claim,
            &crate::debug::driver::DebugOptions::default(),
            &Cvc5LibBackend::new(true, None),
            Some(tempfile::tempdir().unwrap().into_path()),
            &mut NopObserver,
            None,
        )
        .unwrap();
        (run, deps)
    }

    /// Story 23 §4: lockstep and sequential execution must agree in one
    /// direction. If lockstep verifies equal-output on every reachable joint
    /// path, sequential `equal-aborts` and `same-output` (which assume more)
    /// report no failure; if sequential `invariant` fails on a pair and the claim
    /// has no dependencies, lockstep reports an invariant failure somewhere. A
    /// violation is a lowering or engine bug.
    fn assert_consistent(dir: &str, theorem: &str, oracle: &str, lockstep: &LockstepRun) {
        let equal_output_everywhere = lockstep
            .outcome
            .pairs
            .iter()
            .all(|p| matches!(p.equal_output, Verdict::Verified | Verdict::Unreachable));
        if equal_output_everywhere {
            for claim in ["equal-aborts", "same-output"] {
                let (seq, _) = sequential(dir, theorem, oracle, claim);
                assert_eq!(
                    seq.summary.goal_fails, 0,
                    "{oracle}: lockstep verifies equal-output but sequential {claim} fails"
                );
            }
        }
        let (seq, deps) = sequential(dir, theorem, oracle, "invariant");
        if seq.summary.goal_fails > 0 && deps == 0 {
            assert!(
                lockstep
                    .outcome
                    .pairs
                    .iter()
                    .any(|p| p.invariant.is_failure()),
                "{oracle}: sequential invariant fails but lockstep reports no failure"
            );
        }
    }

    #[test]
    fn lockstep_agrees_with_sequential_execution_on_the_acceptance_cases() {
        for (dir, theorem, oracle) in CASES {
            let lockstep = lockstep_easycrypt(dir, theorem, oracle);
            assert_consistent(dir, theorem, oracle, &lockstep);
        }
    }

    #[test]
    fn lockstep_agrees_with_sequential_execution_on_the_rule_oracles() {
        // invariant claims here have no dependencies, so the second direction
        // is exercised for real (`BadState`, `AbortState`)
        for oracle in [
            "Determined",
            "Synced",
            "Split",
            "SplitPruned",
            "OneSided",
            "SyncSample",
            "IndepSample",
            "BadOutput",
            "BadState",
            "AbortDiff",
            "AbortBoth",
            "AbortState",
        ] {
            let lockstep = run_rules(oracle);
            assert_consistent("testdata/lockstep/rules", "T", oracle, &lockstep);
        }
    }

    /// Records the progress events of a lockstep run as owned strings.
    #[derive(Default)]
    struct Events(Vec<String>);

    impl DebugObserver for Events {
        fn on_event(&mut self, ev: &DebugEvent<'_>) {
            #[allow(unreachable_patterns)]
            match ev {
                DebugEvent::Started { .. } => self.0.push("started".into()),
                DebugEvent::JointNode { index, kind } => self.0.push(format!("node {index} {kind}")),
                DebugEvent::JointPairChecked { id, .. } => self.0.push(format!("pair {id}")),
                DebugEvent::StuckPointFound { id, reason, .. } => {
                    self.0.push(format!("stuck {id} {reason}"))
                }
                DebugEvent::LockstepFinished { pairs, stuck, .. } => {
                    self.0.push(format!("finished {pairs} {stuck}"))
                }
                _ => {}
            }
        }
    }

    #[test]
    fn progress_events_report_nodes_pairs_and_stuck_points() {
        let dir = "testdata/lockstep/rules";
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let mut events = Events::default();
        run_lockstep_on(
            ListingKind::Domino,
            &project,
            "T",
            0,
            "StuckOrder",
            &LockstepDebugOptions::default(),
            &Cvc5LibBackend::new(true, None),
            Some(tempfile::tempdir().unwrap().into_path()),
            &mut events,
            None,
        )
        .unwrap();
        assert_eq!(
            events.0,
            [
                "started",
                "node 0 stuck",
                "stuck S1 partner-not-at-head",
                "node 1 sampling-synchronized",
                "node 2 stuck",
                "stuck S2 no-partner-reachable",
                "node 3 terminal-pair",
                "pair J1",
                "finished 1 2",
            ]
        );
    }

    #[test]
    fn an_interrupted_run_leaves_a_partial_trace() {
        let dir = "testdata/lockstep/rules";
        let files = DirectoryFiles::load(Path::new(dir)).unwrap();
        let project = DirectoryProject::load(PathBuf::from(dir), &files).unwrap();
        let out = tempfile::tempdir().unwrap();
        let stop = AtomicBool::new(true);
        run_lockstep_on(
            ListingKind::Domino,
            &project,
            "T",
            0,
            "Split",
            &LockstepDebugOptions::default(),
            &Cvc5LibBackend::new(true, None),
            Some(out.path().to_path_buf()),
            &mut NopObserver,
            Some(&stop),
        )
        .unwrap();
        let trace: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(out.path().join("trace.json")).unwrap())
                .unwrap();
        assert_eq!(trace["stop_reason"]["kind"], "interrupted");
        let text = std::fs::read_to_string(out.path().join("summary.txt")).unwrap();
        assert!(text.contains("STOPPED EARLY (interrupted by Ctrl-C)"), "{text}");
    }

    #[test]
    fn the_summary_names_stuck_points_failures_and_the_stop_reason() {
        let run = run_rules("StuckOrder");
        let text = lockstep_report::render_summary(&run);
        for needle in [
            "COMPLETE",
            "joint paths   1",
            "verified      / verified     1",
            "S1  left sampling",
            "partner-not-at-head",
            "S2  right sampling",
            "no-partner-reachable",
        ] {
            assert!(text.contains(needle), "missing `{needle}` in:\n{text}");
        }

        let run = run_rules("BadState");
        let text = lockstep_report::render_summary(&run);
        assert!(text.contains("state relations failing"), "{text}");
        assert!(text.contains("J1"), "{text}");
    }

    #[test]
    fn the_tree_text_marks_every_node_and_joint_path() {
        let run = run_rules("SplitPruned");
        let text = lockstep_report::render_tree(&run.meta, &run.outcome, &run.summary);
        assert!(text.contains("[0] split"), "{text}");
        assert!(text.contains("pruned, infeasible"), "{text}");
        for id in ["J1", "J2"] {
            assert!(text.contains(id), "{text}");
        }
    }

    /// The `smt/` file of a joint path is self-contained: `base ++ both paths`
    /// answers the vacuity check, and each goal block its own check, as the run
    /// recorded.
    #[test]
    fn a_joint_path_smt_file_reproduces_the_recorded_verdicts() {
        use crate::util::smtsolver::SmtSolverResponse;
        use std::fmt::Write as _;

        for oracle in ["Split", "BadState", "AbortDiff"] {
            let out = tempfile::tempdir().unwrap();
            let run = run_rules_with(
                oracle,
                LockstepDebugOptions {
                    smt_out: SmtOut::All,
                    ..LockstepDebugOptions::default()
                },
                Some(out.path().to_path_buf()),
            );
            let smt = out.path().join("smt");
            for pair in &run.outcome.pairs {
                let text = std::fs::read_to_string(smt.join(format!("{}.smt2", pair.id))).unwrap();
                let code: String = text
                    .lines()
                    .filter(|l| !l.trim_start().starts_with(';'))
                    .fold(String::new(), |mut acc, l| {
                        let _ = writeln!(acc, "{l}");
                        acc
                    });
                // base frame and both paths, then `(check-sat)` for vacuity, then
                // the goal blocks
                let (paths, goals) = code.split_once("(check-sat)\n").unwrap();
                let mut solver = Cvc5LibBackend::new(true, None).new_smtsolver().unwrap();
                solver.write_str(paths).unwrap();
                let vacuity = solver.check_sat().unwrap();
                if matches!(pair.equal_output, Verdict::Unreachable) {
                    assert_eq!(vacuity, SmtSolverResponse::Unsat, "{oracle} {}", pair.id);
                    continue;
                }
                assert_ne!(vacuity, SmtSolverResponse::Unsat, "{oracle} {}", pair.id);
                let answers: Vec<SmtSolverResponse> = goals
                    .split("(push 1)\n")
                    .skip(1)
                    .map(|block| {
                        let goal = block.split_once("\n(check-sat)").unwrap().0;
                        solver.push().unwrap();
                        solver.write_str(goal).unwrap();
                        let answer = solver.check_sat().unwrap();
                        solver.pop().unwrap();
                        answer
                    })
                    .collect();
                let expected: Vec<SmtSolverResponse> = [&pair.equal_output, &pair.invariant]
                    .into_iter()
                    .chain(pair.relations.iter().map(|r| &r.verdict))
                    .map(|v| match v {
                        Verdict::Verified => SmtSolverResponse::Unsat,
                        Verdict::GoalFails { .. } => SmtSolverResponse::Sat,
                        other => panic!("unexpected {other:?}"),
                    })
                    .collect();
                assert_eq!(answers, expected, "{oracle} {}", pair.id);
            }
        }
    }

    #[test]
    fn smt_failures_writes_only_the_failing_joint_paths() {
        let out = tempfile::tempdir().unwrap();
        let run = run_rules_with(
            "Split",
            LockstepDebugOptions::default(),
            Some(out.path().to_path_buf()),
        );
        let smt = out.path().join("smt");
        assert!(smt.join("base.smt2").is_file());
        let present: Vec<bool> = run
            .outcome
            .pairs
            .iter()
            .map(|p| smt.join(format!("{}.smt2", p.id)).is_file())
            .collect();
        assert_eq!(present, [false, true, true, false]);

        let none = tempfile::tempdir().unwrap();
        run_rules_with(
            "Split",
            LockstepDebugOptions {
                smt_out: SmtOut::None,
                ..LockstepDebugOptions::default()
            },
            Some(none.path().to_path_buf()),
        );
        assert!(!none.path().join("smt").exists());
    }
}

#[cfg(test)]
mod throttle_tests {
    use super::*;

    #[test]
    fn partial_flushes_are_limited_to_two_a_second() {
        let t0 = Instant::now();
        let mut throttle = FlushThrottle::new(FLUSH_GAP, t0);
        assert!(!throttle.due(t0), "the initial write just happened");
        assert!(!throttle.due(t0 + Duration::from_millis(499)));
        assert!(throttle.due(t0 + Duration::from_millis(500)));
        assert!(!throttle.due(t0 + Duration::from_millis(600)), "counted from the last flush");
        assert!(throttle.due(t0 + Duration::from_millis(1000)));
        assert!(FLUSH_GAP >= Duration::from_millis(500));
    }
}
