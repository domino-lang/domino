// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino debug` — solver-guided exploration and claim checking.
//!
//! This is the driver the epic exists for: it symbolically executes the left
//! oracle to every terminal (story 05), and for each left terminal explores the
//! right oracle, asking the solver at every terminal pair whether the pair is
//! reachable and whether the claim goal holds. Failures come back pinned to a
//! concrete, human-readable execution path on both sides.
//!
//! ## Encoding
//!
//! A single **base frame** is asserted once at solver level 0
//! ([`base_frame`]): the same declarations, game definitions, constants,
//! invariants and randomness machinery `prove` uses, except
//! [`EquivalenceContext::emit_constant_declarations`] is narrowed with
//! `Some(oracle)` so `<return-{GI}-{O}>` is left free, and the claim's
//! assumptions are asserted positively up front (story 04). Then, per left path,
//! `push` and assert its flat DSA encoding; per right path, `push` and assert
//! that; check reachability (vacuity); `push` and assert the negated goal; check.
//!
//! ## Branch-level pruning (story 08)
//!
//! Story 05's [`execute_streaming_with_oracle`] consults a [`BranchOracle`] at
//! every fork. [`SolverPruner`] is that oracle: it mirrors the executor's DFS on
//! the solver stack (one `push` per `enter`, one `pop` per `leave`) and answers
//! [`Feasibility::Prune`] for a fork whose prefix is `unsat`.
//!
//! - **Verdicts are decoupled from pruning.** The terminal-pair vacuity check
//!   ([`check_pair`]) is **unconditional** — it is what distinguishes
//!   [`Verdict::Unreachable`] from [`Verdict::Verified`], and it is not tied to
//!   the pruning flags.
//! - `check_left` / `check_right` (both **on** by default, disabled with
//!   `--no-check-left` / `--no-check-right`) only decide whether the
//!   corresponding side's `SolverPruner` actually queries the solver and cuts
//!   subtrees. `--no-check-left --no-check-right` reproduces the un-pruned
//!   full-enumeration behaviour exactly.
//! - **Soundness.** The per-path SMT encoding is a plain conjunction
//!   (`decls ++ constraints ++ return_constraint`), so a branch only adds a
//!   conjunct: `base ∧ prefix` `unsat` ⟹ `base ∧ prefix ∧ rest` `unsat` for
//!   every `rest`. Cutting an `unsat` prefix therefore removes only pairs that
//!   would have been `Unreachable`; it can never hide a [`Verdict::GoalFails`].
//!   The converse fails, so the terminal-pair vacuity check stays. If the
//!   per-path encoding ever stops being a plain conjunction, this breaks.
//! - A per-left-path terminal `check_sat` (gated on `check_left`) additionally
//!   prunes a whole left path whose *terminal* is `unsat` — needed because
//!   `no-abort` and the other claim assumptions only bite once
//!   `return_constraint` lands, which is not part of any branch prefix.
//!
//! Only `unsat` ever prunes. `unknown` and timeouts are always explored.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use serde_derive::Serialize;

use crate::debug::claims::{
    aggregate, check_claim, check_claims, obligations, ClaimQuery, PairAborts,
};
use crate::debug::effect::PathEffect;
use crate::debug::exec::{
    execute_streaming_with_oracle, BranchOracle, BranchQuery, ExecError, Feasibility, Side, Step,
    Terminal, TerminalPath,
};
use crate::debug::ir::{
    count_terminals, inline_oracle, InlineError, InlinedOracle, Label, Listing, SiteInfo, SiteKind,
};
use crate::debug::layout::{Layout, ALL_CLAIMS_DIR, DOMINO_DEBUG_DIR};
use crate::debug::progress::{DebugEvent, DebugObserver, SharedObserver};
use crate::debug::render;
use crate::debug::report;
use crate::debug::smtout::{SmtOut, SmtWriter};
use crate::gamehops::equivalence::Equivalence;
use crate::gamehops::GameHop;
use crate::project::Project;
use crate::theorem::{Claim, GameInstance, Theorem};
use crate::transforms::samplify::SampleInfo;
use crate::transforms::theorem_transforms::{
    DebugTransform, EquivalenceTransform, EquivalenceTransformError,
};
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse};
use crate::writers::smt::contexts::EquivalenceContext;
use crate::writers::smt::exprs::SmtExpr;

/// Knobs from the CLI.
#[derive(Debug, Clone, Copy)]
pub struct DebugOptions {
    /// Prune unreachable LEFT branches as they are reached (and whole left paths
    /// whose terminal is `unsat`). Default **on**; `--no-check-left` disables it.
    /// Does **not** affect which verdicts are distinguishable.
    pub check_left: bool,
    /// Prune unreachable RIGHT branches as they are reached, under the current
    /// left path. Default **on**; `--no-check-right` disables it. Does **not**
    /// disable the terminal-pair vacuity check (that is now unconditional).
    pub check_right: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`). A timeout
    /// counts as `unknown` — explored, never pruned.
    pub timeout_ms: Option<u64>,
    /// Give up after this many explored paths (left paths + right paths per left
    /// path). `None` (the default as of story 10) means unlimited — `Ctrl-C` is
    /// then the interactive stop.
    pub max_paths: Option<usize>,
    /// Which per-path SMT files to write under `<out>/smt/` (story 11). Default
    /// [`SmtOut::Failures`].
    pub smt_out: SmtOut,
    /// Also write the raw incremental solver transcript to `transcript.smt2`
    /// (story 11). Off by default — for debugging `domino debug` itself.
    pub transcript: bool,
    /// All-claim runs: stop checking a claim after its first `GoalFails`, for large sweeps.
    /// Without it a failed claim keeps being checked on later pairs — knowing *which* paths
    /// break a claim is the product.
    pub first_failure_per_claim: bool,
}

impl Default for DebugOptions {
    fn default() -> Self {
        Self {
            check_left: true,
            check_right: true,
            timeout_ms: None,
            max_paths: None,
            smt_out: SmtOut::Failures,
            transcript: false,
            first_failure_per_claim: false,
        }
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum DebugError {
    #[error("no theorem named `{name}` in this project")]
    TheoremNotFound { name: String },

    #[error("proofstep {index} is out of range (the theorem has {len} proofsteps: 0..{len})")]
    ProofstepOutOfRange { index: usize, len: usize },

    #[error("proofstep {index} is a {kind}; `domino debug` only supports equivalence proofsteps")]
    ProofstepNotEquivalence { index: usize, kind: &'static str },

    #[error("oracle `{oracle}` is not exported by game instance `{game_inst}`")]
    OracleNotExported { oracle: String, game_inst: String },

    #[error("no claim named `{claim}` for this oracle (available: {})", available.join(", "))]
    ClaimNotFound {
        claim: String,
        available: Vec<String>,
    },

    #[diagnostic(transparent)]
    #[error(transparent)]
    Transform(#[from] EquivalenceTransformError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    Equivalence(#[from] crate::gamehops::equivalence::error::Error),

    #[diagnostic(transparent)]
    #[error(transparent)]
    Inline(#[from] InlineError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    Exec(#[from] ExecError),

    #[diagnostic(transparent)]
    #[error(transparent)]
    EasyCrypt(#[from] crate::writers::easycrypt::EcExportError),

    #[error(transparent)]
    Solver(#[from] crate::util::smtsolver::error::Error),

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

// ---------------------------------------------------------------------------
// The serialisable run structure (story 07 serialises exactly this to trace.json)
// ---------------------------------------------------------------------------

/// Schema version of `trace.json` (see `docs/stories/07-…`). Bump on any
/// breaking change to the serialised shape.
pub const TRACE_SCHEMA: u32 = 9;

/// Why exploration ended. Serialised into `trace.json` (replacing the old bare
/// `partial: bool`); `summary.txt` prints the human-readable form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum StopReason {
    /// Every path the pruner did not cut was explored.
    Completed,
    /// `--max-paths <n>` was reached.
    MaxPaths { limit: usize },
    /// `Ctrl-C`.
    Interrupted,
}

impl StopReason {
    /// `true` unless the run explored everything it set out to.
    pub fn is_partial(self) -> bool {
        !matches!(self, StopReason::Completed)
    }

    /// One-clause description for `summary.txt` / `render_tree` / the viewer.
    pub fn phrase(self) -> String {
        match self {
            StopReason::Completed => "complete".to_string(),
            StopReason::MaxPaths { limit } => format!("--max-paths {limit} reached"),
            StopReason::Interrupted => "interrupted by Ctrl-C".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DebugRun {
    /// `trace.json` schema version. Always [`TRACE_SCHEMA`].
    pub schema: u32,
    /// The strategy that produced this run: `sequential`. Named in every summary header and
    /// in the artifact names (story 19 §4.6).
    pub strategy: &'static str,
    pub theorem: String,
    pub proofstep: usize,
    pub left_game: String,
    pub right_game: String,
    pub oracle: String,
    /// The claim asked about, or `!all-claims!` for an all-claim run.
    pub claim: String,
    /// No `--claim`: the whole obligation set of the oracle was checked on one exploration.
    pub all_claims: bool,
    /// The claims of the run, in the order they are checked. One entry for a single-claim
    /// run. An admitted claim is listed and never checked.
    pub claims: Vec<ClaimInfo>,
    /// The claim is admitted — there is nothing to check. For an all-claim run: every claim is.
    pub admitted: bool,
    /// The output directory. Absolute — **skipped** in `trace.json` so two runs
    /// on the same project produce byte-identical output.
    #[serde(skip)]
    pub out_dir: String,
    /// Wall-clock time of the run so far. Updated immediately before every
    /// [`report::flush`] (once per left path) and once more at the end, so
    /// `main.rs` can print the concise stdout report without threading its own
    /// clock through the CLI. `#[serde(skip)]` — `trace.json` and `index.html`
    /// stay byte-deterministic (story 07), exactly like `out_dir`. Only
    /// `summary.txt`'s sibling on stdout (`render_summary`) reads it.
    #[serde(skip)]
    pub elapsed: Duration,
    /// The options this run was launched with.
    pub options: OptionsView,
    /// The base declarations asserted once at solver level 0, rendered. This is
    /// also the head of `transcript.smt2` up to the first `(push 1)`; kept here
    /// so `index.html` is self-contained. Empty for an admitted claim.
    pub base_frame_smt: String,
    /// The negated claim goal — `(assert (not …))` — checked at every (left,
    /// right) terminal pair after the vacuity check. One per run: it depends on
    /// the claim and the oracle, not on the path. Empty for an admitted claim.
    /// The viewer's `Claim assertion` section renders it (story 13). For an all-claim run:
    /// each claim's own dependencies and negated goal, under a `; claim <name>` comment.
    pub goal_smt: String,
    /// The left game instance's inlined listing (line `n` == `Label` `n`).
    pub left_listing: String,
    /// The right game instance's inlined listing (numbered independently).
    pub right_listing: String,
    /// Per-label metadata for the left listing (branch/assert/return/... sites).
    pub left_sites: BTreeMap<Label, SiteView>,
    /// Per-label metadata for the right listing.
    pub right_sites: BTreeMap<Label, SiteView>,
    pub left_paths: Vec<LeftPath>,
    /// LEFT branches cut by `check_left` before any terminal below them was
    /// reached. Rendered as top-level rows alongside `left_paths`.
    pub left_pruned_branches: Vec<PrunedBranch>,
    pub summary: Summary,
    /// Per-claim verdict counts over every checked pair. Empty for a single-claim run, whose
    /// counts are `summary`'s.
    pub claim_summaries: Vec<ClaimSummary>,
    /// Solver queries the run asked (story 19). Deterministic, so safe in `trace.json`.
    pub queries: QueryCounts,
    /// Number of syntactic left terminals (`ir::count_terminals`) — the "of N"
    /// denominator in `summary.txt`'s left-path line. `0` for an admitted claim.
    /// Deterministic; safe in `trace.json`.
    pub left_syntactic: u64,
    /// Why exploration ended (story 12). Replaces the old `partial: bool` — kept
    /// at the same field position so the serialised order stays predictable.
    /// `Completed` unless `--max-paths` fired or a `Ctrl-C` landed.
    pub stop_reason: StopReason,
}

/// One claim of the run's claim set.
#[derive(Debug, Clone, Serialize)]
pub struct ClaimInfo {
    pub name: String,
    /// Its own declared dependencies (`no-abort`, project lemmas, …).
    pub dependencies: Vec<String>,
    pub admitted: bool,
}

/// One claim's verdicts over every pair of an all-claim run.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct ClaimSummary {
    pub claim: String,
    pub verified: usize,
    /// Unreachable because the pair itself is infeasible.
    pub unreachable_pair: usize,
    /// Unreachable because this claim's own dependency is false on the pair.
    pub unreachable_dependency: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
    /// `--first-failure-per-claim`: pairs this claim was not checked on after it failed.
    pub skipped: usize,
}

/// Solver queries a run asked, split by what they were for.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct QueryCounts {
    /// Branch pruning, left-terminal reachability and pair vacuity: what the *exploration*
    /// costs. An all-claim run pays it once for the whole claim set.
    pub exploration: usize,
    /// The claim checks at terminal pairs: these scale with the claim count.
    pub claims: usize,
}

/// One fork the solver proved unreachable, so its subtree was never explored.
#[derive(Debug, Clone, Serialize)]
pub struct PrunedBranch {
    /// Stable id in the same namespace as path ids: `"p2"` for a left prune,
    /// `"4.p1"` for a right prune under left path `#4`.
    pub id: String,
    /// Steps to and *including* the cut decision.
    pub steps: Vec<StepView>,
    /// Label of the forking statement.
    pub label: usize,
    /// Its rendered source line.
    pub line: String,
    /// `then` / `else` / `assert-holds` / `assert-fails` / `unwrap-some` /
    /// `unwrap-none` — the child that was cut.
    pub decision: String,
    /// Line ranges executed on the way to (and including) the cut fork, in the
    /// same shape as [`LeftPath::lines`] / [`RightPath::lines`] (story 16).
    /// Serialised as `[[3,9],[12,12]]`.
    pub lines: Vec<[usize; 2]>,
}

/// The CLI knobs, in a shape that serialises cleanly into `trace.json`.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct OptionsView {
    pub check_left: bool,
    pub check_right: bool,
    pub timeout_ms: Option<u64>,
    /// `null` in `trace.json` when unlimited (story 10).
    pub max_paths: Option<usize>,
    /// Per-path SMT file coverage (story 11): `none` / `failures` / `all` /
    /// `deltas`, kebab-case in `trace.json`.
    pub smt: SmtOut,
    /// Whether the monolithic `transcript.smt2` was written (story 11).
    pub transcript: bool,
    pub first_failure_per_claim: bool,
}

impl From<&DebugOptions> for OptionsView {
    fn from(o: &DebugOptions) -> Self {
        Self {
            check_left: o.check_left,
            check_right: o.check_right,
            timeout_ms: o.timeout_ms,
            max_paths: o.max_paths,
            smt: o.smt_out,
            transcript: o.transcript,
            first_failure_per_claim: o.first_failure_per_claim,
        }
    }
}

/// One entry of [`Listing::sites`], flattened for serialisation (the
/// `SourceSpan` back-reference is dropped — the viewer works off line numbers).
#[derive(Debug, Clone, Serialize)]
pub struct SiteView {
    /// `assign` / `sample` / `unwrap` / `branch` / `assert` / `call` / `return` /
    /// `abort`.
    pub kind: String,
    /// The rendered source line, trimmed.
    pub line: String,
    pub pkg_inst: String,
    pub oracle: String,
    /// Frame depth: 0 for the entry oracle's own body, 1 for a directly inlined
    /// callee, and so on.
    pub depth: usize,
}

impl From<&SiteInfo> for SiteView {
    fn from(s: &SiteInfo) -> Self {
        let kind = match s.kind {
            SiteKind::Assign => "assign",
            SiteKind::Sample => "sample",
            SiteKind::Unwrap => "unwrap",
            SiteKind::Branch => "branch",
            SiteKind::Assert => "assert",
            SiteKind::Call => "call",
            SiteKind::Return => "return",
            SiteKind::Abort => "abort",
        };
        Self {
            kind: kind.to_string(),
            line: s.line.clone(),
            pkg_inst: s.pkg_inst_name.clone(),
            oracle: s.oracle_name.clone(),
            depth: s.depth,
        }
    }
}

pub(crate) fn sites_view(listing: &Listing) -> BTreeMap<Label, SiteView> {
    listing
        .sites
        .iter()
        .map(|(label, info)| (*label, SiteView::from(info)))
        .collect()
}

#[derive(Debug, Clone, Serialize)]
pub struct LeftPath {
    /// `"1"`, `"2"`, … in exploration order. Rendered `#1`.
    pub id: String,
    pub steps: Vec<StepView>,
    pub terminal: TerminalView,
    /// What this path computed — symbolic return value + new state, over the
    /// oracle arguments and old state (story 18). `None` for an abort terminal.
    /// Pure display; the `smt` field stays authoritative.
    pub effect: Option<PathEffect>,
    /// Line ranges of the left listing this path executed (story 16),
    /// serialised as `[[3,9],[12,12]]`. Sorted, non-overlapping, includes the
    /// terminal line.
    pub lines: Vec<[usize; 2]>,
    /// `false` if `check_left` proved this path's *terminal* unsat and pruned it
    /// (its right side was not explored).
    pub reachable: bool,
    /// The exact SMT asserted for this path (`decls` ++ `constraints` ++
    /// `return_constraint`), rendered.
    pub smt: Vec<String>,
    pub right_paths: Vec<RightPath>,
    /// RIGHT branches `check_right` cut under this left path (only meaningful
    /// relative to this left path's context).
    pub pruned_branches: Vec<PrunedBranch>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RightPath {
    /// `"1.1"`, `"1.2"`, … Rendered `#1.1`.
    pub id: String,
    pub steps: Vec<StepView>,
    pub terminal: TerminalView,
    /// What this path computed — symbolic return value + new state (story 18).
    /// `None` for an abort terminal. Pure display.
    pub effect: Option<PathEffect>,
    /// Line ranges of the right listing this path executed (story 16), same
    /// shape as [`LeftPath::lines`].
    pub lines: Vec<[usize; 2]>,
    /// For an all-claim run, the verdict that stands for the pair: a failure if any claim
    /// failed, `verified` if any claim verified, else `unreachable`. See
    /// [`crate::debug::claims::aggregate`].
    pub verdict: Verdict,
    /// What each claim said about this pair. Empty for a single-claim run.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub claims: Vec<ClaimVerdict>,
    /// The solver model, inline, for `goal-fails` / `inconclusive` pairs — so
    /// `index.html` needs no sidecar files. `None` otherwise. The same text is
    /// also written to `models/<id>.smt2` (referenced by [`Verdict`]).
    pub model_smt: Option<String>,
    pub smt: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StepView {
    pub label: usize,
    pub line: String,
    /// `then` / `else` / `assert-holds` / `assert-fails` / `unwrap-some` /
    /// `unwrap-none`.
    pub decision: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct TerminalView {
    pub label: usize,
    pub line: String,
    pub is_abort: bool,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum Verdict {
    /// Goal check `unsat` — the claim holds on this pair.
    Verified,
    /// Infeasible under the assumptions in force — **not** the same as `Verified`. The
    /// `reason` says how far the infeasibility reaches (story 19).
    Unreachable { reason: Unreachability },
    /// Goal check `sat` — the claim fails; `model` is the written model file
    /// (relative to the output directory).
    GoalFails { model: String },
    /// Goal check `unknown` / timed out.
    Inconclusive { model: Option<String> },
}

/// The scope of an [`Verdict::Unreachable`]. Neither flavour is a failure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum Unreachability {
    /// The pair itself cannot happen: the vacuity check was unsat.
    PairInfeasible,
    /// The pair happens, but this claim's premise is false on it. `dependency` names the one
    /// that failed, e.g. `no-abort`.
    DependencyFalse { dependency: String },
}

impl Verdict {
    /// The pair cannot happen: [`Verdict::Unreachable`] with [`Unreachability::PairInfeasible`].
    pub fn pair_infeasible() -> Verdict {
        Verdict::Unreachable {
            reason: Unreachability::PairInfeasible,
        }
    }

    /// `verified`, `unreachable`, `goal-fails` or `inconclusive`.
    pub fn slug(&self) -> &'static str {
        match self {
            Verdict::Verified => "verified",
            Verdict::Unreachable { .. } => "unreachable",
            Verdict::GoalFails { .. } => "goal-fails",
            Verdict::Inconclusive { .. } => "inconclusive",
        }
    }

    /// The claim does not hold, or the solver could not tell.
    pub fn is_failure(&self) -> bool {
        matches!(self, Verdict::GoalFails { .. } | Verdict::Inconclusive { .. })
    }
}

/// What one claim of the oracle's obligation set said about one terminal pair.
#[derive(Debug, Clone, Serialize)]
pub struct ClaimVerdict {
    pub claim: String,
    pub verdict: Verdict,
    /// Sub-verdicts of `invariant`, present only when it is neither verified nor unreachable
    /// (lockstep execution). Empty for every other claim.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub relations: Vec<crate::debug::lockstep::RelationVerdict>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct Summary {
    pub left_paths: usize,
    /// Whole left paths cut at their terminal (`check_left`).
    pub left_pruned: usize,
    /// LEFT forks cut at branch level (`check_left`).
    pub left_pruned_branches: usize,
    pub right_paths: usize,
    /// RIGHT forks cut at branch level (`check_right`), summed over left paths.
    pub right_pruned_branches: usize,
    /// Times the sibling shortcut (skip a `check_sat` when the other child was
    /// pruned and the parent was a definite `Sat`) fired. Diagnostic only.
    pub sibling_shortcuts: usize,
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

impl DebugRun {
    /// Exploration stopped early (`--max-paths` or `Ctrl-C`) — results are
    /// partial. Thin accessor over [`StopReason::is_partial`] so the many old
    /// `run.partial` call sites need only a one-character change.
    pub fn partial(&self) -> bool {
        self.stop_reason.is_partial()
    }

    /// Every explored pair is `Verified` or `Unreachable` and exploration
    /// finished. This is the process exit-code criterion.
    pub fn is_ok(&self) -> bool {
        !self.partial() && self.summary.goal_fails == 0 && self.summary.inconclusive == 0
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// The strategy name of [`run_debug_command`], in [`DebugRun::strategy`] and in every artifact
/// name.
pub const SEQUENTIAL: &str = "sequential";

/// Run `domino debug` for one oracle and return the (serialisable) run: `claim_name` narrows it
/// to one claim, whose dependencies stay in the base frame; without it the whole obligation set
/// is checked on one exploration — an **all-claim run** (story 19).
///
/// Writes the sequential artifacts under `out` (defaulting to
/// `_build/debug/domino/<theorem>/<left>-<right>/<oracle>/<claim>/`, `!all-claims!` in place of
/// `<claim>` for an all-claim run).
#[allow(clippy::too_many_arguments)]
pub fn run_debug_command<P, B>(
    project: &P,
    req_proof: &str,
    req_proofstep: usize,
    oracle: &str,
    claim_name: Option<&str>,
    opts: &DebugOptions,
    backend: &B,
    out: Option<PathBuf>,
    observer: &mut dyn DebugObserver,
    stop: Option<&AtomicBool>,
) -> Result<DebugRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
    // Wall-clock for the concise stdout report only. Copied into
    // `run.elapsed` before every flush; that field is `#[serde(skip)]`, so
    // `trace.json` / `index.html` stay byte-deterministic (story 07).
    let started = Instant::now();
    let layout = Layout::Strategy(SEQUENTIAL);

    let theorem = project
        .get_theorem(req_proof)
        .ok_or_else(|| DebugError::TheoremNotFound {
            name: req_proof.to_string(),
        })?;

    let eq = equivalence_of(theorem, req_proofstep)?;

    // Two transforms of the same theorem:
    //  * `EquivalenceTransform` (with `treeify`) feeds the `EquivalenceContext` —
    //    `emit_game_definitions` compiles every oracle body into the monolithic
    //    nested SMT term and needs `treeify` to have run.
    //  * `DebugTransform` (no `treeify`) feeds `inline_oracle` + the symbolic
    //    executor, which need the 1:1 statement structure the labels depend on.
    // `samplify` / `sample_max_counter_extractor` run *before* `treeify`, so
    // `sample_info`, argument names, `<return-…>` names and game-state constants
    // are identical between the two — the per-path DSA encoding lines up with the
    // base frame.
    //
    // A third transform exists and is deliberately *not* used here:
    // `EasyCryptTransform` (story 16) runs `easycryptify` instead of `treeify`,
    // lowering every `assert`/`abort`/early `return` into EasyCrypt's single-exit
    // shape (no `abort`, `Maybe`-typed signatures). It is what `domino easycrypt`
    // exports and what `domino easycrypt debug` walks; `domino debug` is the Domino
    // listing only (story 19), so this stays `DebugTransform` and a Domino listing keeps
    // rendering `assert` as `assert`.
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
    let left_si = sample_info_of(eq.left_name());
    let right_si = sample_info_of(eq.right_name());

    // Validate the oracle is exported before anything panics deeper down.
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

    // Resolve the claims: the oracle's whole obligation set (the user-written proof tree plus
    // the generated package/game invariant claims — the same set `prove` checks), narrowed to
    // one claim when asked.
    let all_obligations = obligations(&eqctx, eq, oracle);
    let claims: Vec<Claim> = match claim_name {
        Some(name) => vec![all_obligations
            .iter()
            .find(|claim| claim.name() == name)
            .cloned()
            .ok_or_else(|| DebugError::ClaimNotFound {
                claim: name.to_string(),
                available: all_obligations.iter().map(|c| c.name().to_string()).collect(),
            })?],
        None => all_obligations,
    };
    let all_claims = claim_name.is_none();
    let claim_label = claim_name.unwrap_or(ALL_CLAIMS_DIR);
    let admitted = claims.iter().all(Claim::is_admitted);

    observer.on_event(&DebugEvent::Started {
        oracle,
        claim: claim_label,
        admitted,
    });

    let left_inl = inline_oracle(left_inst, oracle)?;
    let right_inl = inline_oracle(right_inst, oracle)?;

    // Solver-free syntactic path counts — upper bounds the progress display
    // shows as `k/N` and the "of N syntactic" denominator in `summary.txt`.
    // Skipped when there is nothing to check (nothing between `Started { admitted }` and
    // `Finished`).
    let (left_syntactic, right_syntactic) = if admitted {
        (0, 0)
    } else {
        (count_terminals(&left_inl), count_terminals(&right_inl))
    };
    if !admitted {
        observer.on_event(&DebugEvent::Totals {
            left_total: left_syntactic,
            right_total: right_syntactic,
        });
        // Story 11 §6: `--smt all` writes one full base frame per pair. Warn
        // once, up front, when that is likely to be large.
        if opts.smt_out == SmtOut::All && left_syntactic.saturating_mul(right_syntactic) > 50 {
            eprintln!(
                "debug: --smt all writes a self-contained copy of the base frame for every \
                 explored pair (up to {} × {} here) — this can be hundreds of MB; consider \
                 --smt failures or --smt deltas",
                left_syntactic, right_syntactic
            );
        }
    }
    let observer: SharedObserver = RefCell::new(observer);

    let out_dir = out.unwrap_or_else(|| {
        let mut path = project.get_root_dir();
        path.push(DOMINO_DEBUG_DIR);
        path.push(eq.theorem_name());
        path.push(format!("{}-{}", eq.left_name(), eq.right_name()));
        path.push(oracle);
        path.push(claim_label);
        path
    });
    std::fs::create_dir_all(&out_dir)?;
    std::fs::create_dir_all(layout.path(&out_dir, "models"))?;

    let mut run = DebugRun {
        schema: TRACE_SCHEMA,
        strategy: SEQUENTIAL,
        theorem: eq.theorem_name().to_string(),
        proofstep: req_proofstep,
        left_game: eq.left_name().to_string(),
        right_game: eq.right_name().to_string(),
        oracle: oracle.to_string(),
        claim: claim_label.to_string(),
        all_claims,
        claims: claims
            .iter()
            .map(|c| ClaimInfo {
                name: c.name().to_string(),
                dependencies: c.dependencies().to_vec(),
                admitted: c.is_admitted(),
            })
            .collect(),
        admitted,
        out_dir: out_dir.display().to_string(),
        elapsed: Duration::ZERO,
        options: OptionsView::from(opts),
        base_frame_smt: String::new(),
        goal_smt: String::new(),
        left_listing: left_inl.listing.text.clone(),
        right_listing: right_inl.listing.text.clone(),
        left_sites: sites_view(&left_inl.listing),
        right_sites: sites_view(&right_inl.listing),
        left_paths: Vec::new(),
        left_pruned_branches: Vec::new(),
        summary: Summary::default(),
        claim_summaries: Vec::new(),
        queries: QueryCounts::default(),
        left_syntactic,
        stop_reason: StopReason::Completed,
    };

    if !admitted {
        // A single claim keeps its dependencies in the base frame — lemmas help prune, and a
        // narrowed run should get that benefit. An all-claim run asserts only what every claim
        // shares: each claim's own dependencies wait for the terminal pair.
        let base = match claims.as_slice() {
            [claim] if !all_claims => base_frame(&eqctx, oracle, claim),
            _ => shared_base_frame(&eqctx, oracle),
        };
        run.base_frame_smt = base
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        // Story 11: the per-path `smt/` tree is the primary artifact. The
        // monolithic `transcript.smt2` is opt-in (`--transcript`) — it doubles
        // every byte the driver sends and is only useful for debugging the
        // driver itself.
        let smt_writer = SmtWriter::new(&out_dir, layout, opts.smt_out, &run)?;
        // Computed once here (story 11): the negated claim goals. The pair check used to
        // re-derive them per pair; the `smt/` files embed their text.
        let checking = Checking::new(&eqctx, &claims, oracle, all_claims, opts, layout);
        run.goal_smt = checking.goal_text();

        let mut solver = if opts.transcript {
            std::fs::create_dir_all(layout.path(&out_dir, ""))?;
            let transcript = std::fs::File::create(layout.path(&out_dir, "transcript.smt2"))?;
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

        // The left `BranchOracle` and the terminal handler both need the solver,
        // at different (never overlapping) points of the executor's DFS — hence
        // the `RefCell`. See `SolverPruner`.
        let solver = RefCell::new(solver);
        let counters = Counters::default();
        explore_paths(
            &solver, &left_inl, &right_inl, left_inst, right_inst, left_si, right_si, opts,
            &out_dir, &observer, stop, &smt_writer, &checking, &counters, started, &mut run,
        )?;
        run.queries = counters.snapshot();
        run.claim_summaries = checking.claim_summaries(&run);

        solver.into_inner().close();
    }

    std::fs::write(
        out_dir.join("inlined.txt"),
        render::side_by_side(&run.left_listing, &run.right_listing),
    )?;
    run.elapsed = started.elapsed();
    report::flush(&run, &out_dir)?;

    observer.borrow_mut().on_event(&DebugEvent::Finished {
        summary: run.summary,
        stop_reason: run.stop_reason,
    });

    Ok(run)
}

/// The equivalence proved at `proofstep` of `theorem`; a hybrid counts as its
/// underlying equivalence, as in `prove`.
pub(crate) fn equivalence_of<'t>(
    theorem: &'t Theorem<'_>,
    proofstep: usize,
) -> Result<&'t Equivalence, DebugError> {
    let hop = theorem
        .game_hops
        .get(proofstep)
        .ok_or(DebugError::ProofstepOutOfRange {
            index: proofstep,
            len: theorem.game_hops.len(),
        })?;
    match hop {
        GameHop::Equivalence(eq) => Ok(eq),
        GameHop::Hybrid(hyb) => Ok(hyb.equivalence()),
        GameHop::Reduction(_) => Err(DebugError::ProofstepNotEquivalence {
            index: proofstep,
            kind: "reduction",
        }),
        GameHop::Conjecture(_) => Err(DebugError::ProofstepNotEquivalence {
            index: proofstep,
            kind: "conjecture",
        }),
    }
}

// ---------------------------------------------------------------------------
// Base frame
// ---------------------------------------------------------------------------

/// Everything every claim of this oracle shares, asserted once at solver level 0: the same
/// declarations, game definitions, constants, invariants and randomness machinery `prove` uses,
/// with `emit_constant_declarations` narrowed to `Some(oracle)` (story 04), and then, positively,
/// what no claim can do without — the randomness-mapping condition and the invariants on the old
/// states (main, per game, per package).
pub(crate) fn shared_base_frame<'a>(
    eqctx: &'a EquivalenceContext<'a>,
    oracle: &str,
) -> Vec<SmtExpr> {
    let mut base = vec![SmtExpr::Comment(" domino debug — base frame ".to_string())];
    base.extend(eqctx.emit_base_declarations());
    base.extend(eqctx.emit_theorem_paramfuncs());
    base.extend(eqctx.emit_game_definitions());
    base.extend(eqctx.emit_constant_declarations(Some(oracle)));
    base.extend(eqctx.emit_auto_randomness(oracle));
    base.extend(eqctx.emit_invariant());
    base.extend(eqctx.emit_return_value_helpers(oracle));
    base.extend(eqctx.emit_randomness_mapping_condition(oracle));
    base.push(SmtExpr::Comment(" claim assumptions ".to_string()));
    base.extend(eqctx.emit_shared_assumptions(oracle));
    base
}

/// [`shared_base_frame`] plus `claim`'s own declared dependencies — a single-claim run's frame
/// (story 04). The dependencies prune: `no-abort` makes every aborting path `unsat` at the fork.
pub(crate) fn base_frame<'a>(
    eqctx: &'a EquivalenceContext<'a>,
    oracle: &str,
    claim: &Claim,
) -> Vec<SmtExpr> {
    let mut base = shared_base_frame(eqctx, oracle);
    base.extend(eqctx.emit_claim_own_assumptions(claim, oracle));
    base
}

// ---------------------------------------------------------------------------
// What is checked at a terminal pair
// ---------------------------------------------------------------------------

/// Solver queries, counted as they are asked. Shared by the pruners and the pair checks.
#[derive(Default)]
struct Counters {
    exploration: Cell<usize>,
    claims: Cell<usize>,
}

impl Counters {
    fn snapshot(&self) -> QueryCounts {
        QueryCounts {
            exploration: self.exploration.get(),
            claims: self.claims.get(),
        }
    }

    fn explored(&self) {
        self.exploration.set(self.exploration.get() + 1);
    }
}

/// What the claims said about one terminal pair.
struct PairCheck {
    verdict: Verdict,
    model_smt: Option<String>,
    /// One per claim checked, for an all-claim run; empty for a single-claim run.
    claims: Vec<ClaimVerdict>,
}

/// The claims of a run and how a terminal pair is checked against them.
///
/// **Single claim:** its dependencies are already in the base frame, so a pair costs the
/// vacuity check and one goal query.
///
/// **All-claim:** the pair's path conditions and the shared assumptions are on the stack; the
/// vacuity check is asked once, and then each claim is one `push` / `check-sat` / `pop` on top
/// ([`check_claim`]) — differing only in its own dependencies and its negated goal.
struct Checking {
    /// Empty for an admitted-only run.
    claims: Vec<ClaimQuery>,
    /// `false`: one claim, whose dependencies are in the base frame.
    all: bool,
    layout: Layout,
    first_failure_per_claim: bool,
    /// `--first-failure-per-claim`: claims that have failed, and the pairs each was then spared.
    failed: RefCell<BTreeSet<String>>,
    skipped: RefCell<BTreeMap<String, usize>>,
}

impl Checking {
    fn new(
        eqctx: &EquivalenceContext<'_>,
        claims: &[Claim],
        oracle: &str,
        all: bool,
        opts: &DebugOptions,
        layout: Layout,
    ) -> Self {
        let queries = claims
            .iter()
            .filter(|claim| !claim.is_admitted())
            .map(|claim| {
                let mut query = ClaimQuery::of(eqctx, claim, oracle);
                if !all {
                    // already in the base frame: asserting them again would only cost
                    query.dependencies.clear();
                }
                query
            })
            .collect();
        Self {
            claims: queries,
            all,
            layout,
            first_failure_per_claim: opts.first_failure_per_claim,
            failed: RefCell::default(),
            skipped: RefCell::default(),
        }
    }

    /// The text `trace.json`'s `goal_smt` and the viewer's `Claim assertion` section show.
    fn goal_text(&self) -> String {
        match self.claims.as_slice() {
            [only] if !self.all => only.negated.to_string(),
            claims => claims
                .iter()
                .map(|claim| {
                    let mut text = format!("; claim {}\n", claim.name);
                    for (_, dependency) in &claim.dependencies {
                        text.push_str(&format!("{dependency}\n"));
                    }
                    text.push_str(&claim.negated.to_string());
                    text
                })
                .collect::<Vec<_>>()
                .join("\n"),
        }
    }

    /// One block per claim for the `smt/` pair files: its dependencies, then its goal.
    fn goals(&self) -> Vec<GoalBlock> {
        self.claims
            .iter()
            .map(|claim| GoalBlock {
                claim: claim.name.clone(),
                dependencies: claim
                    .dependencies
                    .iter()
                    .map(|(_, assertion)| assertion.to_string())
                    .collect(),
                negated: claim.negated.to_string(),
            })
            .collect()
    }

    /// The vacuity check, unconditional, then the claims. The stack holds the base frame and
    /// both paths, and is as it was on return.
    fn check_pair<S: SmtSolver>(
        &self,
        solver: &mut S,
        rid: &str,
        aborts: PairAborts,
        out_dir: &Path,
        counters: &Counters,
    ) -> Result<PairCheck, DebugError> {
        // Vacuity (overview §3) — UNCONDITIONAL as of story 08. `unsat` here means the pair
        // cannot happen; it is **not** the same as `Verified`.
        counters.explored();
        if matches!(solver.check_sat()?, SmtSolverResponse::Unsat) {
            let claims = if self.all {
                self.claims
                    .iter()
                    .map(|claim| ClaimVerdict {
                        claim: claim.name.clone(),
                        verdict: Verdict::pair_infeasible(),
                        relations: Vec::new(),
                    })
                    .collect()
            } else {
                Vec::new()
            };
            return Ok(PairCheck {
                verdict: Verdict::pair_infeasible(),
                model_smt: None,
                claims,
            });
        }

        let mut queries = 0usize;
        let check = if self.all {
            let checked = check_claims(
                solver,
                &self.claims,
                aborts,
                out_dir,
                self.layout,
                rid,
                &mut queries,
                |claim| {
                    let spared =
                        self.first_failure_per_claim && self.failed.borrow().contains(claim);
                    if spared {
                        *self.skipped.borrow_mut().entry(claim.to_string()).or_default() += 1;
                    }
                    spared
                },
            )?;
            if self.first_failure_per_claim {
                for (claim, _) in &checked {
                    if matches!(claim.verdict, Verdict::GoalFails { .. }) {
                        self.failed.borrow_mut().insert(claim.claim.clone());
                    }
                }
            }
            let (verdict, model_smt) = aggregate(&checked);
            PairCheck {
                verdict,
                model_smt,
                claims: checked.into_iter().map(|(claim, _)| claim).collect(),
            }
        } else {
            // Story 11: the negated goal was computed once, in `Checking::new` (its text
            // also lands in `smt/`).
            let [claim] = self.claims.as_slice() else {
                unreachable!("a single-claim run checks one claim");
            };
            let (verdict, model_smt) = check_claim(
                solver, claim, aborts, out_dir, self.layout, rid, &mut queries,
            )?;
            PairCheck {
                verdict,
                model_smt,
                claims: Vec::new(),
            }
        };
        counters.claims.set(counters.claims.get() + queries);
        Ok(check)
    }

    /// Verdict counts per claim over the pairs of `run`, for an all-claim run.
    fn claim_summaries(&self, run: &DebugRun) -> Vec<ClaimSummary> {
        if !self.all {
            return Vec::new();
        }
        let skipped = self.skipped.borrow();
        run.claims
            .iter()
            .filter(|info| !info.admitted)
            .map(|info| {
                let mut summary = ClaimSummary {
                    claim: info.name.clone(),
                    skipped: skipped.get(&info.name).copied().unwrap_or(0),
                    ..ClaimSummary::default()
                };
                let verdicts = run
                    .left_paths
                    .iter()
                    .flat_map(|lp| &lp.right_paths)
                    .flat_map(|rp| &rp.claims)
                    .filter(|c| c.claim == info.name);
                for c in verdicts {
                    match &c.verdict {
                        Verdict::Verified => summary.verified += 1,
                        Verdict::Unreachable {
                            reason: Unreachability::PairInfeasible,
                        } => summary.unreachable_pair += 1,
                        Verdict::Unreachable {
                            reason: Unreachability::DependencyFalse { .. },
                        } => summary.unreachable_dependency += 1,
                        Verdict::GoalFails { .. } => summary.goal_fails += 1,
                        Verdict::Inconclusive { .. } => summary.inconclusive += 1,
                    }
                }
                summary
            })
            .collect()
    }
}

/// One claim's part of a pair's `smt/` file.
pub struct GoalBlock {
    pub claim: String,
    /// Assertions of the claim's own dependencies (empty in a single-claim run: they are in
    /// the base frame).
    pub dependencies: Vec<String>,
    pub negated: String,
}

// ---------------------------------------------------------------------------
// Exploration
// ---------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn explore_paths<'o, S: SmtSolver>(
    solver: &RefCell<S>,
    left_inl: &InlinedOracle,
    right_inl: &InlinedOracle,
    left_inst: &GameInstance,
    right_inst: &GameInstance,
    left_si: &SampleInfo,
    right_si: &SampleInfo,
    opts: &DebugOptions,
    out_dir: &Path,
    observer: &SharedObserver<'o>,
    stop: Option<&AtomicBool>,
    smt_writer: &SmtWriter,
    checking: &Checking,
    counters: &Counters,
    started: Instant,
    run: &mut DebugRun,
) -> Result<(), DebugError> {
    let mut left_pruner = SolverPruner::new(
        solver,
        opts.check_left,
        &left_inl.listing,
        String::new(),
        observer,
        Side::Left,
        stop,
        counters,
    );
    let mut explored = 0usize;
    let mut left_counter = 0usize;
    let mut right_shortcuts = 0usize;
    let mut fatal: Option<DebugError> = None;
    let mut cancelled = false;

    {
        let fatal = &mut fatal;
        let explored = &mut explored;
        let left_counter = &mut left_counter;
        let right_shortcuts = &mut right_shortcuts;
        let run = &mut *run;

        let mut on_left = |lp: &TerminalPath| -> ControlFlow<()> {
            if stop.is_some_and(|s| s.load(Ordering::Relaxed)) {
                run.stop_reason = StopReason::Interrupted;
                return ControlFlow::Break(());
            }
            *explored += 1;
            *left_counter += 1;
            if let Some(m) = opts.max_paths {
                if *explored > m {
                    run.stop_reason = StopReason::MaxPaths { limit: m };
                    return ControlFlow::Break(());
                }
            }
            let index = *left_counter;
            let lid = format!("{index}");
            observer.borrow_mut().on_event(&DebugEvent::LeftPathStarted {
                index,
                id: &lid,
            });
            match handle_left_path(
                solver,
                checking,
                counters,
                opts,
                out_dir,
                right_inl,
                right_inst,
                right_si,
                &left_inl.listing,
                &lid,
                lp,
                observer,
                stop,
                smt_writer,
                explored,
                run,
            ) {
                Ok((lv, shortcuts)) => {
                    *right_shortcuts += shortcuts;
                    if !lv.reachable {
                        observer
                            .borrow_mut()
                            .on_event(&DebugEvent::LeftPathPruned { id: &lid });
                    }
                    run.left_paths.push(lv);
                    run.summary = summarize(&run.left_paths, &run.left_pruned_branches);
                    run.queries = counters.snapshot();
                    observer.borrow_mut().on_event(&DebugEvent::LeftPathFinished {
                        index,
                        running: run.summary,
                    });
                    run.elapsed = started.elapsed();
                    if let Err(e) = report::flush(run, out_dir) {
                        *fatal = Some(DebugError::Io(e));
                        return ControlFlow::Break(());
                    }
                    ControlFlow::Continue(())
                }
                Err(e) => {
                    *fatal = Some(e);
                    ControlFlow::Break(())
                }
            }
        };

        // `ExecError::Cancelled` (a `Ctrl-C` caught inside the left pruning
        // sweep) is a stop, not a failure — record it and fall through to the
        // partial-run handling like `--max-paths` does.
        match execute_streaming_with_oracle(
            left_inl,
            left_inst,
            left_si,
            Side::Left,
            None,
            Some(&mut left_pruner),
            &mut on_left,
        ) {
            Ok(()) => {}
            Err(ExecError::Cancelled) => cancelled = true,
            Err(e) => return Err(e.into()),
        }
    }
    if cancelled {
        run.stop_reason = StopReason::Interrupted;
    }

    if let Some(e) = left_pruner.err.take() {
        return Err(e.into());
    }
    if let Some(e) = fatal {
        return Err(e);
    }

    // Push/pop discipline: every `enter` was balanced by a `leave`, so the
    // solver stack is back at the level-0 baseline.
    debug_assert_eq!(
        left_pruner.depth(),
        0,
        "solver stack not balanced after left exploration"
    );
    run.left_pruned_branches = left_pruner.take_pruned();

    run.summary = summarize(&run.left_paths, &run.left_pruned_branches);
    run.summary.sibling_shortcuts = left_pruner.shortcut_fired + right_shortcuts;
    Ok(())
}

/// One left terminal: assert its (delta) encoding on top of the branch prefix the
/// left [`SolverPruner`] already put on the stack, optionally check the terminal
/// is reachable, then explore the right oracle under it.
///
/// On entry the solver stack is at this left path's branch depth; on return it is
/// back there (one extra `push`/`pop` wraps the whole terminal so sibling left
/// paths do not inherit it).
#[allow(clippy::too_many_arguments)]
fn handle_left_path<'o, S: SmtSolver>(
    solver: &RefCell<S>,
    checking: &Checking,
    counters: &Counters,
    opts: &DebugOptions,
    out_dir: &Path,
    right_inl: &InlinedOracle,
    right_inst: &GameInstance,
    right_si: &SampleInfo,
    left_listing: &Listing,
    lid: &str,
    lp: &TerminalPath,
    observer: &SharedObserver<'o>,
    stop: Option<&AtomicBool>,
    smt_writer: &SmtWriter,
    explored: &mut usize,
    run: &mut DebugRun,
) -> Result<(LeftPath, usize), DebugError> {
    {
        let mut s = solver.borrow_mut();
        s.push()?;
        write_path_delta(&mut *s, lp)?;
    }

    // Per-left-path terminal check (gated on `check_left`). Not redundant with
    // branch pruning: `no-abort` and the other claim assumptions constrain
    // `<is-abort-Left>` / `<return-value-Left>`, which are tied to the path only
    // by `return_constraint` — so a left abort path is `unsat` at its *terminal*,
    // never at a *branch*.
    let reachable = if opts.check_left {
        counters.explored();
        !matches!(solver.borrow_mut().check_sat()?, SmtSolverResponse::Unsat)
    } else {
        true
    };

    let mut left_view = LeftPath {
        id: lid.to_string(),
        steps: steps_view(left_listing, &lp.steps),
        terminal: terminal_view(left_listing, &lp.terminal),
        effect: lp.effect.clone(),
        lines: lines_view(&lp.lines),
        reachable,
        smt: render_path_smt(lp),
        right_paths: Vec::new(),
        pruned_branches: Vec::new(),
    };
    let mut right_shortcuts = 0usize;

    // Story 11: `smt/<lid>/left.smt2` — this left path's own delta, written for
    // every explored left path (independent of `reachable` and of the pair
    // coverage mode), so it can be `cat`-reassembled with `base.smt2`.
    smt_writer.write_left(lid, &left_view)?;

    if reachable {
        let mut right_pruner = SolverPruner::new(
            solver,
            opts.check_right,
            &right_inl.listing,
            format!("{lid}."),
            observer,
            Side::Right,
            stop,
            counters,
        );
        let mut right_counter = 0usize;
        let mut fatal: Option<DebugError> = None;
        let mut cancelled = false;

        {
            let left_view = &mut left_view;
            let fatal = &mut fatal;
            let explored = &mut *explored;
            let run = &mut *run;
            let right_counter = &mut right_counter;

            let mut on_right = |rp: &TerminalPath| -> ControlFlow<()> {
                if stop.is_some_and(|s| s.load(Ordering::Relaxed)) {
                    run.stop_reason = StopReason::Interrupted;
                    return ControlFlow::Break(());
                }
                *explored += 1;
                if let Some(m) = opts.max_paths {
                    if *explored > m {
                        run.stop_reason = StopReason::MaxPaths { limit: m };
                        return ControlFlow::Break(());
                    }
                }
                *right_counter += 1;
                let rid = format!("{lid}.{}", *right_counter);
                match handle_right_path(
                    solver,
                    checking,
                    counters,
                    out_dir,
                    &right_inl.listing,
                    &rid,
                    lp.terminal.is_abort(),
                    rp,
                    observer,
                ) {
                    Ok(rv) => {
                        // Story 11: `smt/<lid>/<r>.smt2` for the pairs the
                        // coverage mode wants (a no-op otherwise).
                        if let Err(e) =
                            smt_writer.write_pair(lid, left_view, &rv, &checking.goals())
                        {
                            *fatal = Some(DebugError::Io(e));
                            return ControlFlow::Break(());
                        }
                        left_view.right_paths.push(rv);
                        ControlFlow::Continue(())
                    }
                    Err(e) => {
                        *fatal = Some(e);
                        ControlFlow::Break(())
                    }
                }
            };

            match execute_streaming_with_oracle(
                right_inl,
                right_inst,
                right_si,
                Side::Right,
                None,
                Some(&mut right_pruner),
                &mut on_right,
            ) {
                Ok(()) => {}
                Err(ExecError::Cancelled) => cancelled = true,
                Err(e) => return Err(e.into()),
            }
        }
        if cancelled {
            run.stop_reason = StopReason::Interrupted;
        }

        if let Some(e) = right_pruner.err.take() {
            return Err(e.into());
        }
        if let Some(e) = fatal {
            return Err(e);
        }
        // Back at this left path's terminal level after the right exploration.
        debug_assert_eq!(
            right_pruner.depth(),
            0,
            "solver stack not balanced after right exploration"
        );
        right_shortcuts = right_pruner.shortcut_fired;
        left_view.pruned_branches = right_pruner.take_pruned();
    }

    solver.borrow_mut().pop()?;
    Ok((left_view, right_shortcuts))
}

/// One right terminal, under the current left path: assert its (delta) encoding
/// and run the terminal-pair checks.
#[allow(clippy::too_many_arguments)]
fn handle_right_path<'o, S: SmtSolver>(
    solver: &RefCell<S>,
    checking: &Checking,
    counters: &Counters,
    out_dir: &Path,
    right_listing: &Listing,
    rid: &str,
    left_aborts: bool,
    rp: &TerminalPath,
    observer: &SharedObserver<'o>,
) -> Result<RightPath, DebugError> {
    let PairCheck {
        verdict,
        model_smt,
        claims,
    } = {
        let mut s = solver.borrow_mut();
        s.push()?;
        write_path_delta(&mut *s, rp)?;
        let t0 = Instant::now();
        let aborts = PairAborts {
            left: left_aborts,
            right: rp.terminal.is_abort(),
        };
        let check = checking.check_pair(&mut *s, rid, aborts, out_dir, counters)?;
        s.pop()?;
        drop(s);
        observer.borrow_mut().on_event(&DebugEvent::PairChecked {
            id: rid,
            verdict: &check.verdict,
            elapsed: t0.elapsed(),
        });
        check
    };
    Ok(RightPath {
        id: rid.to_string(),
        steps: steps_view(right_listing, &rp.steps),
        terminal: terminal_view(right_listing, &rp.terminal),
        effect: rp.effect.clone(),
        lines: lines_view(&rp.lines),
        verdict,
        claims,
        model_smt,
        smt: render_path_smt(rp),
    })
}

/// Assert only the part of `path` not already on the solver stack — the branch
/// prefix a [`SolverPruner`] already asserted incrementally. `reported_*` are `0`
/// when no pruner was active on that side, so this then asserts the whole path.
fn write_path_delta<S: SmtSolver>(
    solver: &mut S,
    path: &TerminalPath,
) -> Result<(), DebugError> {
    for entry in &path.decls[path.reported_decls..] {
        solver.write_smt(entry.clone())?;
    }
    for entry in &path.constraints[path.reported_constraints..] {
        solver.write_smt(entry.clone())?;
    }
    solver.write_smt(path.return_constraint.clone())?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The solver-backed BranchOracle
// ---------------------------------------------------------------------------

/// A [`BranchOracle`] backed by the solver stack: `push` + write-delta on
/// `enter`, `pop` on `leave`, and [`Feasibility::Prune`] for a fork whose prefix
/// the solver reports `unsat`. It mirrors the executor's DFS exactly, so at any
/// point the stack holds the base frame (plus, for a right pruner, the current
/// left path) and one level per open `enter` scope.
///
/// **Only `unsat` prunes.** `Sat`, `Unknown`, timeouts and stashed solver errors
/// are all `Explore`.
struct SolverPruner<'s, 'o, S: SmtSolver> {
    solver: &'s RefCell<S>,
    /// `false` ⇒ never query, never prune. Still `push`es/`pop`s and writes the
    /// per-branch delta, so the stack stays in lockstep and the terminal
    /// `reported_*` offsets line up.
    enabled: bool,
    listing: &'s Listing,
    /// `""` for the left pruner, `"<lid>."` for a per-left-path right pruner.
    id_prefix: String,
    /// Progress observer — a [`DebugEvent::BranchPruned`] is emitted for every
    /// fork this pruner cuts (story 09 / story 08 §3.6 hook).
    observer: &'s SharedObserver<'o>,
    /// Which side this pruner runs on, for [`DebugEvent::BranchPruned`].
    side: Side,
    /// `Ctrl-C` flag (story 10). Checked at the top of every `enter`, so an
    /// interrupt lands *inside* a branch-pruning sweep, not only at path
    /// boundaries. `enter` returns [`ExecError::Cancelled`] before opening its
    /// scope, so the solver stack still unwinds balanced.
    stop: Option<&'s AtomicBool>,
    counters: &'s Counters,
    /// Per open scope: was this context a definite `Sat`? (`false` for `Unknown`,
    /// disabled, or a stashed error.)
    known_sat: Vec<bool>,
    /// Per open scope: was it entered as a prune (so `leave` is immediate and the
    /// "previous sibling pruned" signal must survive to the next sibling)?
    scope_pruned: Vec<bool>,
    /// The fork sibling that just finished was a prune.
    last_sibling_pruned: bool,
    pruned: Vec<PrunedBranch>,
    n_pruned: usize,
    /// Times the §3.2-step-3 sibling shortcut fired (for the report).
    shortcut_fired: usize,
    /// Solver errors cannot cross `enter`'s `ExecError` return type — stashed
    /// here and re-raised by the driver.
    err: Option<crate::util::smtsolver::error::Error>,
}

impl<'s, 'o, S: SmtSolver> SolverPruner<'s, 'o, S> {
    fn new(
        solver: &'s RefCell<S>,
        enabled: bool,
        listing: &'s Listing,
        id_prefix: String,
        observer: &'s SharedObserver<'o>,
        side: Side,
        stop: Option<&'s AtomicBool>,
        counters: &'s Counters,
    ) -> Self {
        Self {
            solver,
            enabled,
            listing,
            id_prefix,
            observer,
            side,
            stop,
            counters,
            known_sat: Vec::new(),
            scope_pruned: Vec::new(),
            last_sibling_pruned: false,
            pruned: Vec::new(),
            n_pruned: 0,
            shortcut_fired: 0,
            err: None,
        }
    }

    fn take_pruned(&mut self) -> Vec<PrunedBranch> {
        std::mem::take(&mut self.pruned)
    }

    /// Open `enter` scopes — equivalently, the number of solver levels this
    /// pruner has pushed and not yet popped. `0` means balanced.
    fn depth(&self) -> usize {
        self.known_sat.len()
    }

    fn push_and_write(&self, query: &BranchQuery<'_>) -> crate::util::smtsolver::Result<()> {
        let mut s = self.solver.borrow_mut();
        s.push()?;
        for d in query.decls {
            s.write_smt(d.clone())?;
        }
        for c in query.constraints {
            s.write_smt(c.clone())?;
        }
        Ok(())
    }

    fn record_prune(&mut self, query: &BranchQuery<'_>) {
        self.n_pruned += 1;
        let line = self
            .listing
            .sites
            .get(&query.label)
            .map(|s| s.line.clone())
            .unwrap_or_default();
        let id = format!("{}p{}", self.id_prefix, self.n_pruned);
        self.observer.borrow_mut().on_event(&DebugEvent::BranchPruned {
            side: self.side,
            id: &id,
            label: query.label,
        });
        let mut visited = query.visited.to_vec();
        self.pruned.push(PrunedBranch {
            id,
            steps: steps_view(self.listing, query.steps),
            label: query.label,
            line,
            decision: query.decision.as_str().to_string(),
            lines: lines_view(&crate::debug::exec::ranges(&mut visited)),
        });
    }

    fn open_scope(&mut self, known_sat: bool, pruned: bool) {
        self.known_sat.push(known_sat);
        self.scope_pruned.push(pruned);
    }
}

impl<S: SmtSolver> BranchOracle for SolverPruner<'_, '_, S> {
    fn enter(&mut self, query: &BranchQuery<'_>) -> Result<Feasibility, ExecError> {
        // Story 10: a set `Ctrl-C` flag stops the walk here — before any `push`
        // or `check-sat`, so the solver stack stays balanced and the driver can
        // treat this as `partial`, not an error.
        if self.stop.is_some_and(|s| s.load(Ordering::Relaxed)) {
            return Err(ExecError::Cancelled);
        }

        let parent_sat = self.known_sat.last().copied();
        let prev_sibling_pruned = self.last_sibling_pruned;

        if let Err(e) = self.push_and_write(query) {
            self.err.get_or_insert(e);
            self.open_scope(false, false);
            return Ok(Feasibility::Explore);
        }

        if !self.enabled {
            self.open_scope(false, false);
            return Ok(Feasibility::Explore);
        }

        // Sibling shortcut (§3.2 step 3): if the previous sibling `c` was pruned
        // (`base ∧ P ∧ c` unsat) and the parent context `base ∧ P` was a definite
        // `Sat`, then `base ∧ P ∧ ¬c` must be `Sat` — skip the query. Not valid
        // when the parent was only `Unknown`.
        if query.sibling == 1 && prev_sibling_pruned && parent_sat == Some(true) {
            self.shortcut_fired += 1;
            self.open_scope(true, false);
            return Ok(Feasibility::Explore);
        }

        self.counters.explored();
        let ans = self.solver.borrow_mut().check_sat();
        match ans {
            Ok(SmtSolverResponse::Unsat) => {
                self.record_prune(query);
                self.open_scope(false, true);
                Ok(Feasibility::Prune)
            }
            Ok(SmtSolverResponse::Sat) => {
                self.open_scope(true, false);
                Ok(Feasibility::Explore)
            }
            Ok(SmtSolverResponse::Unknown) => {
                self.open_scope(false, false);
                Ok(Feasibility::Explore)
            }
            Err(e) => {
                self.err.get_or_insert(e);
                self.open_scope(false, false);
                Ok(Feasibility::Explore)
            }
        }
    }

    fn leave(&mut self) {
        self.known_sat.pop();
        self.last_sibling_pruned = self.scope_pruned.pop().unwrap_or(false);
        if let Err(e) = self.solver.borrow_mut().pop() {
            self.err.get_or_insert(e);
        }
    }
}

/// Writes the current model to `<layout>/models/<id>.smt2` and returns
/// `(path relative to out_dir, model text)`.
pub(crate) fn write_model<S: SmtSolver>(
    solver: &mut S,
    out_dir: &Path,
    layout: Layout,
    id: &str,
) -> Result<(String, String), DebugError> {
    let (model, _) = solver.get_model()?;
    let rel = layout.rel(&format!("models/{id}.smt2"));
    std::fs::write(out_dir.join(&rel), &model)?;
    Ok((rel, model))
}

/// Collect up to `cap` terminal paths; the `bool` says the cap was hit.
/// Un-pruned enumeration — used only by the per-path DSA consistency test.
#[cfg(all(test, feature = "cvc5-lib"))]
fn collect_paths(
    inl: &InlinedOracle,
    inst: &GameInstance,
    sample_info: &SampleInfo,
    side: Side,
    cap: usize,
) -> Result<(Vec<TerminalPath>, bool), ExecError> {
    let mut paths = Vec::new();
    let mut capped = false;
    execute_streaming_with_oracle(inl, inst, sample_info, side, None, None, &mut |path| {
        if paths.len() >= cap {
            capped = true;
            ControlFlow::Break(())
        } else {
            paths.push(path.clone());
            ControlFlow::Continue(())
        }
    })?;
    Ok((paths, capped))
}

pub(crate) fn steps_view(listing: &Listing, steps: &[Step]) -> Vec<StepView> {
    steps
        .iter()
        .map(|step| StepView {
            label: step.label,
            line: listing
                .sites
                .get(&step.label)
                .map(|s| s.line.clone())
                .unwrap_or_default(),
            decision: step.decision.as_str().to_string(),
        })
        .collect()
}

pub(crate) fn terminal_view(listing: &Listing, terminal: &Terminal) -> TerminalView {
    let label = terminal.label();
    TerminalView {
        label,
        line: listing
            .sites
            .get(&label)
            .map(|s| s.line.clone())
            .unwrap_or_default(),
        is_abort: terminal.is_abort(),
    }
}

/// [`TerminalPath::lines`] / a pruned branch's prefix, into the array-of-arrays
/// shape `trace.json` uses (story 16).
pub(crate) fn lines_view(lines: &[(Label, Label)]) -> Vec<[usize; 2]> {
    lines.iter().map(|&(a, b)| [a, b]).collect()
}

fn render_path_smt(path: &TerminalPath) -> Vec<String> {
    path.decls
        .iter()
        .chain(&path.constraints)
        .chain(std::iter::once(&path.return_constraint))
        .map(|e| e.to_string())
        .collect()
}

fn summarize(left_paths: &[LeftPath], left_pruned_branches: &[PrunedBranch]) -> Summary {
    let mut summary = Summary {
        left_paths: left_paths.len(),
        left_pruned_branches: left_pruned_branches.len(),
        ..Summary::default()
    };
    for lp in left_paths {
        if !lp.reachable {
            summary.left_pruned += 1;
        }
        summary.right_pruned_branches += lp.pruned_branches.len();
        for rp in &lp.right_paths {
            summary.right_paths += 1;
            match rp.verdict {
                Verdict::Verified => summary.verified += 1,
                Verdict::Unreachable { .. } => summary.unreachable += 1,
                Verdict::GoalFails { .. } => summary.goal_fails += 1,
                Verdict::Inconclusive { .. } => summary.inconclusive += 1,
            }
        }
    }
    summary
}

// ---------------------------------------------------------------------------
// stdout rendering
// ---------------------------------------------------------------------------

/// The full per-left-path execution tree (the format agreed with the project
/// owner). Written to `summary.txt` as of story 17 — before that it went to
/// stdout, where the concise `report::render_summary` now prints instead. Still
/// used verbatim as the assertion message in several tests here.
pub fn render_tree(run: &DebugRun) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();

    let _ = writeln!(
        out,
        "theorem {}, proofstep {} ({} == {})",
        run.theorem, run.proofstep, run.left_game, run.right_game
    );
    let _ = writeln!(out, "oracle {}, claim {}", run.oracle, run.claim);
    let _ = writeln!(out, "strategy {}", run.strategy);
    let admitted: Vec<&str> = run
        .claims
        .iter()
        .filter(|c| c.admitted)
        .map(|c| c.name.as_str())
        .collect();
    if run.all_claims && !admitted.is_empty() {
        let _ = writeln!(out, "admitted, not checked: {}", admitted.join(", "));
    }

    if run.admitted {
        let _ = writeln!(out, "\nclaim is admitted — nothing to check.");
        return out;
    }

    let _ = writeln!(out, "listing: {}/inlined.txt", run.out_dir);
    let _ = writeln!(
        out,
        "(left and right line numbers are independent — they index different columns of inlined.txt)"
    );

    for lp in &run.left_paths {
        let _ = writeln!(out, "\nleft path #{}:", lp.id);
        for step in &lp.steps {
            let _ = writeln!(out, "  L{} {}  -> {}", step.label, step.line, step.decision);
        }
        let _ = writeln!(
            out,
            "  L{} {}",
            lp.terminal.label, lp.terminal.line
        );

        if !lp.reachable {
            let _ = writeln!(out, "  [unsat: left path unreachable — pruned]");
            continue;
        }

        let _ = writeln!(out, "\n  right paths under #{}:", lp.id);
        for rp in &lp.right_paths {
            let steps: String = rp
                .steps
                .iter()
                .map(|s| format!("L{} {} -> {}", s.label, s.line, s.decision))
                .collect::<Vec<_>>()
                .join("   ");
            let terminal = format!("L{} {}", rp.terminal.label, rp.terminal.line);
            let sep = if steps.is_empty() { "" } else { "   " };
            let note = match &rp.verdict {
                Verdict::Unreachable { reason } if rp.claims.is_empty() => format!(
                    " ({})",
                    describe_unreachable(reason, &lp.terminal, &rp.terminal)
                ),
                _ => String::new(),
            };
            let _ = writeln!(
                out,
                "    #{}  {}{}{}   {}{}",
                rp.id,
                steps,
                sep,
                terminal,
                render_verdict(&rp.verdict),
                note
            );
            // an all-claim run: what each claim said about the pair
            for checked in &rp.claims {
                let note = match &checked.verdict {
                    Verdict::Unreachable { reason } => format!(
                        " — {}",
                        describe_unreachable(reason, &lp.terminal, &rp.terminal)
                    ),
                    _ => String::new(),
                };
                let _ = writeln!(
                    out,
                    "        {:<28} {}{}",
                    checked.claim,
                    render_verdict(&checked.verdict),
                    note
                );
            }
        }
        if !lp.pruned_branches.is_empty() {
            let _ = writeln!(out, "\n    pruned under #{}:", lp.id);
            for pb in &lp.pruned_branches {
                let _ = writeln!(
                    out,
                    "    #{}  L{} {} -> {}   [unsat: branch pruned]",
                    pb.id, pb.label, pb.line, pb.decision
                );
            }
        }
    }

    if !run.left_pruned_branches.is_empty() {
        let _ = writeln!(out, "\npruned left branches:");
        for pb in &run.left_pruned_branches {
            let _ = writeln!(
                out,
                "  #{}  L{} {} -> {}   [unsat: branch pruned]",
                pb.id, pb.label, pb.line, pb.decision
            );
        }
    }

    let s = &run.summary;
    let branches_pruned = s.left_pruned_branches + s.right_pruned_branches;
    let _ = writeln!(
        out,
        "\nsummary: {} left paths{}, {} right paths{}; {} GOAL FAILS, {} verified, {} unreachable, {} inconclusive{}",
        s.left_paths,
        if s.left_pruned > 0 {
            format!(" ({} pruned)", s.left_pruned)
        } else {
            String::new()
        },
        s.right_paths,
        if branches_pruned > 0 {
            format!(" ({branches_pruned} branches pruned)")
        } else {
            String::new()
        },
        s.goal_fails,
        s.verified,
        s.unreachable,
        s.inconclusive,
        if run.partial() {
            format!(
                "\n(PARTIAL: {} — results are incomplete)",
                run.stop_reason.phrase()
            )
        } else {
            String::new()
        },
    );

    out
}

/// Why a pair is unreachable, in the words of the terminals: `left aborts at L27, and this
/// claim assumes no-abort`. Naming the abort is what keeps an all-green all-claim run from
/// looking like a proof.
pub(crate) fn describe_unreachable(
    reason: &Unreachability,
    left: &TerminalView,
    right: &TerminalView,
) -> String {
    match reason {
        Unreachability::PairInfeasible => "pair infeasible".to_string(),
        Unreachability::DependencyFalse { dependency } => {
            let aborts: Vec<String> = [("left", left), ("right", right)]
                .into_iter()
                .filter(|(_, t)| t.is_abort)
                .map(|(side, t)| format!("{side} aborts at L{}", t.label))
                .collect();
            if aborts.is_empty() {
                format!("this claim assumes {dependency}, which is false here")
            } else {
                format!("{}, and this claim assumes {dependency}", aborts.join(" and "))
            }
        }
    }
}

fn render_verdict(verdict: &Verdict) -> String {
    match verdict {
        Verdict::Verified => "[unsat: ok]".to_string(),
        Verdict::Unreachable { .. } => "[unsat: unreachable]".to_string(),
        Verdict::GoalFails { model } => format!("[sat: GOAL FAILS]  {model}"),
        Verdict::Inconclusive { model: Some(model) } => format!("[unknown: inconclusive]  {model}"),
        Verdict::Inconclusive { model: None } => "[unknown: inconclusive]".to_string(),
    }
}

#[cfg(all(test, feature = "cvc5-lib"))]
mod tests {
    use super::*;
    use crate::debug::progress::{DebugEvent, NopObserver};
    use std::fmt::Write as _;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;
    use std::sync::atomic::AtomicBool;

    fn with_project<R>(dir: &str, f: impl FnOnce(&DirectoryProject) -> R) -> R {
        let files = DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
        let proj = DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
        f(&proj)
    }

    fn run_in_tmp(
        dir: &str,
        theorem: &str,
        oracle: &str,
        claim: &str,
        opts: DebugOptions,
    ) -> DebugRun {
        run_in_tmp_with(dir, theorem, oracle, claim, opts, &mut NopObserver, None)
    }

    fn run_in_tmp_with(
        dir: &str,
        theorem: &str,
        oracle: &str,
        claim: &str,
        opts: DebugOptions,
        observer: &mut dyn DebugObserver,
        stop: Option<&AtomicBool>,
    ) -> DebugRun {
        with_project(dir, |proj| {
            // `into_path` keeps the dir around after the test so artifacts can be
            // inspected on failure (and so `run.out_dir` stays valid).
            let out = tempfile::tempdir().unwrap().into_path();
            let backend = Cvc5LibBackend::new(true, opts.timeout_ms);
            run_debug_command(
                proj, theorem, 0, oracle, Some(claim), &opts, &backend, Some(out), observer, stop,
            )
            .unwrap()
        })
    }

    /// Records events as owned, comparable summaries — `DebugEvent` borrows from
    /// the in-flight `DebugRun`, so a keep-around observer must project.
    #[derive(Default)]
    struct RecordingObserver {
        events: Vec<String>,
        left_started: Vec<usize>,
        left_finished: Vec<usize>,
        last_summary: Option<Summary>,
        totals: Option<(u64, u64)>,
    }

    impl DebugObserver for RecordingObserver {
        fn on_event(&mut self, ev: &DebugEvent<'_>) {
            #[allow(unreachable_patterns)] // `DebugEvent` is `#[non_exhaustive]`
            match ev {
                DebugEvent::Started { .. } => self.events.push("Started".into()),
                DebugEvent::Totals {
                    left_total,
                    right_total,
                } => {
                    self.totals = Some((*left_total, *right_total));
                    self.events.push("Totals".into());
                }
                DebugEvent::LeftPathStarted { index, .. } => {
                    self.left_started.push(*index);
                    self.events.push("LeftPathStarted".into());
                }
                DebugEvent::LeftPathPruned { .. } => self.events.push("LeftPathPruned".into()),
                DebugEvent::PairChecked { .. } => self.events.push("PairChecked".into()),
                DebugEvent::BranchPruned { .. } => self.events.push("BranchPruned".into()),
                DebugEvent::LeftPathFinished { index, running } => {
                    self.left_finished.push(*index);
                    self.last_summary = Some(*running);
                    self.events.push("LeftPathFinished".into());
                }
                DebugEvent::Finished { summary, .. } => {
                    self.last_summary = Some(*summary);
                    self.events.push("Finished".into());
                }
                _ => {}
            }
        }
    }

    /// story 05 deferred this: per left path the DSA encoding must agree with the
    /// monolithic oracle function. We check it via the real base frame + the
    /// per-path constraints, negating `<return> = <constructed>` and expecting
    /// `unsat`.
    #[test]
    fn per_path_dsa_agrees_with_the_oracle_function() {
        with_project("example-projects/hello-world", |proj| {
            let theorem = proj.get_theorem("Proof").unwrap();
            // eqctx (base frame) from the treeified transform; paths from the
            // non-treeified one — same split as `run_debug_command`.
            let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(theorem).unwrap();
            let eq = match &theorem_eq.game_hops[0] {
                GameHop::Equivalence(eq) => eq,
                _ => unreachable!(),
            };
            let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
            eqctx.load_invariants(proj).unwrap();

            let (theorem_dbg, auxs_dbg) = DebugTransform.transform_theorem(theorem).unwrap();
            let left_inst = theorem_dbg.find_game_instance(eq.left_name()).unwrap();
            let left_si = &auxs_dbg
                .iter()
                .find(|(n, _)| n == eq.left_name())
                .unwrap()
                .1
                .sample_info;
            let inl = inline_oracle(left_inst, "UsefulOracle").unwrap();
            let paths = collect_paths(&inl, left_inst, left_si, Side::Left, 64)
                .unwrap()
                .0;
            assert!(!paths.is_empty());

            let backend = Cvc5LibBackend::new(false, None);
            let mut solver = backend.new_smtsolver().unwrap();
            // base with `None` so `<return-…>` is constrained to the oracle function.
            for entry in eqctx.emit_base_declarations() {
                solver.write_smt(entry).unwrap();
            }
            for entry in eqctx.emit_theorem_paramfuncs() {
                solver.write_smt(entry).unwrap();
            }
            for entry in eqctx.emit_game_definitions() {
                solver.write_smt(entry).unwrap();
            }
            for entry in eqctx.emit_constant_declarations(None) {
                solver.write_smt(entry).unwrap();
            }
            for entry in eqctx.emit_auto_randomness("UsefulOracle") {
                solver.write_smt(entry).unwrap();
            }

            for path in &paths {
                solver.push().unwrap();
                for entry in path.decls.iter().chain(&path.constraints) {
                    solver.write_smt(entry.clone()).unwrap();
                }
                // `return_constraint` is `(assert (= <return-…> <constructed>))`.
                let eq_term = match &path.return_constraint {
                    SmtExpr::List(items) => items[1].clone(),
                    other => panic!("unexpected return_constraint shape: {other:?}"),
                };
                solver.push().unwrap();
                solver
                    .write_smt(SmtExpr::List(vec![
                        "assert".into(),
                        SmtExpr::List(vec!["not".into(), eq_term]),
                    ]))
                    .unwrap();
                assert_eq!(
                    solver.check_sat().unwrap(),
                    SmtSolverResponse::Unsat,
                    "per-path DSA disagrees with the oracle function"
                );
                solver.pop().unwrap();
                solver.pop().unwrap();
            }
        });
    }

    /// Story 13: `DebugRun.goal_smt` is the exact text the driver asserts at
    /// every terminal pair — `eqctx.emit_claim_goal_negated(&claim, oracle)`
    /// rendered once. Non-empty for a non-admitted run.
    #[test]
    fn goal_smt_equals_the_negated_claim_goal() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions::default(),
        );
        assert!(!run.admitted);
        assert!(!run.goal_smt.is_empty(), "goal_smt must be populated");

        // Rebuild the exact `EquivalenceContext` `run_debug_command` used and
        // re-derive the goal independently.
        with_project("example-projects/kem-dem/kem-dem-cca-ssp", |proj| {
            let theorem = proj.get_theorem("kem_dem_cca_ssp").unwrap();
            let (theorem_eq, auxs_eq) = EquivalenceTransform.transform_theorem(theorem).unwrap();
            let eq = match &theorem_eq.game_hops[0] {
                GameHop::Equivalence(eq) => eq,
                _ => unreachable!(),
            };
            let mut eqctx = EquivalenceContext::new(eq, &theorem_eq, &auxs_eq);
            eqctx.load_invariants(proj).unwrap();

            let mut claims = eq.proof_tree_by_oracle_name("PKGEN");
            claims.extend(eqctx.generate_game_or_package_invariant_claims());
            let claim = claims
                .iter()
                .find(|c| c.name() == "same-output")
                .cloned()
                .unwrap();

            let expected = eqctx.emit_claim_goal_negated(&claim, "PKGEN").to_string();
            assert_eq!(run.goal_smt, expected);
        });

        // And it is in trace.json verbatim.
        let parsed: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("sequential_trace.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(parsed["schema"], 9);
        assert_eq!(parsed["goal_smt"], run.goal_smt);
    }

    /// Story 13: an admitted claim checks nothing, so `goal_smt` stays empty.
    #[test]
    fn goal_smt_is_empty_for_an_admitted_claim() {
        let run = run_in_tmp(
            "testdata/story19/deps",
            "T",
            "Admitted",
            "skipped",
            DebugOptions::default(),
        );
        assert!(run.admitted);
        assert!(run.goal_smt.is_empty());
    }

    /// Story 18: every returning left/right path carries an `effect`; aborts
    /// carry `null`; and adding the effect keeps `trace.json` byte-identical
    /// across two runs of the same project (nothing iterates a `HashMap`).
    #[test]
    fn trace_carries_an_effect_for_every_returning_path() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKENC",
            "same-output",
            DebugOptions::default(),
        );
        let mut returning = 0;
        for lp in &run.left_paths {
            if lp.terminal.is_abort {
                assert!(lp.effect.is_none(), "left #{} abort has an effect", lp.id);
            } else {
                assert!(lp.effect.is_some(), "left #{} return has no effect", lp.id);
                returning += 1;
            }
            for rp in &lp.right_paths {
                if rp.terminal.is_abort {
                    assert!(rp.effect.is_none(), "right #{} abort has an effect", rp.id);
                } else {
                    assert!(rp.effect.is_some(), "right #{} return has no effect", rp.id);
                }
            }
        }
        assert!(returning > 0);

        let trace = std::path::Path::new(&run.out_dir).join("sequential_trace.json");
        let a = std::fs::read_to_string(&trace).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&a).unwrap();
        assert_eq!(parsed["schema"], 9);
        // effect is present in the serialised shape.
        assert!(a.contains("\"effect\""));

        let run2 = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKENC",
            "same-output",
            DebugOptions::default(),
        );
        let b = std::fs::read_to_string(std::path::Path::new(&run2.out_dir).join("sequential_trace.json"))
            .unwrap();
        assert_eq!(a, b, "sequential_trace.json not byte-identical across runs");
    }

    #[test]
    fn hello_world_same_output_is_all_green() {
        let run = run_in_tmp(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions::default(),
        );
        assert!(!run.admitted);
        assert!(run.summary.goal_fails == 0, "{}", render_tree(&run));
        assert!(run.is_ok(), "{}", render_tree(&run));
        // Story 11: `transcript.smt2` is opt-in and absent by default.
        assert!(
            !std::path::Path::new(&run.out_dir).join("sequential/transcript.smt2").exists(),
            "transcript.smt2 must not be written without --transcript"
        );
        // The `smt/` tree is the default artifact: base frame + one delta per
        // explored left path.
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        assert!(smt.join("base.smt2").exists());
        for lp in &run.left_paths {
            assert!(
                smt.join(&lp.id).join("left.smt2").exists(),
                "missing smt/{}/left.smt2",
                lp.id
            );
        }
    }

    /// Story 11: `--transcript` re-enables `transcript.smt2`, and the story-06
    /// assertions on it still hold (a coherent incremental session).
    #[test]
    fn transcript_flag_re_enables_the_monolithic_transcript() {
        let run = run_in_tmp(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions {
                transcript: true,
                ..DebugOptions::default()
            },
        );
        let transcript =
            std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("sequential/transcript.smt2"))
                .unwrap();
        assert!(transcript.contains("(check-sat)"));
        assert!(transcript.contains("(push 1)") && transcript.contains("(pop 1)"));
    }

    /// Story 11: `--smt none` writes no `smt/` directory at all.
    #[test]
    fn smt_none_writes_no_smt_directory() {
        let run = run_in_tmp(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions {
                smt_out: SmtOut::None,
                ..DebugOptions::default()
            },
        );
        assert!(!std::path::Path::new(&run.out_dir).join("sequential/smt").exists());
    }

    /// Story 11 — the self-containment property. An emitted pair file's body is
    /// exactly `base ++ left.smt ++ right.smt ++ vacuity ++ negated goal`. We
    /// re-feed `base.smt2 ++ lp.smt ++ rp.smt` to a fresh solver (this is what
    /// the file contains, minus comments) and confirm the vacuity + goal answers
    /// reproduce the verdict `domino debug` recorded — i.e. nothing else was on
    /// the solver stack and the `reported_*` watermarks really are prefixes.
    #[test]
    fn emitted_pair_file_reproduces_the_recorded_verdict() {
        use crate::util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse};

        let run = run_in_tmp(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions {
                smt_out: SmtOut::All,
                ..DebugOptions::default()
            },
        );
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        let base = std::fs::read_to_string(smt.join("base.smt2")).unwrap();

        let mut checked = 0usize;
        for lp in &run.left_paths {
            for rp in &lp.right_paths {
                let rtail = rp.id.rsplit('.').next().unwrap();
                let file = smt.join(&lp.id).join(format!("{rtail}.smt2"));
                let text = std::fs::read_to_string(&file).unwrap();
                assert!(text.contains("(get-model)") && text.contains("(pop 1)"));

                // The goal text is what the file puts after `(push 1)`.
                let goal = text
                    .rsplit_once("(push 1)\n")
                    .unwrap()
                    .1
                    .split_once("\n(check-sat)")
                    .unwrap()
                    .0;

                let backend = Cvc5LibBackend::new(true, None);
                let mut s = backend.new_smtsolver().unwrap();
                s.write_str(&base).unwrap();
                for line in lp.smt.iter().chain(rp.smt.iter()) {
                    s.write_str(line).unwrap();
                    s.write_str("\n").unwrap();
                }
                let vac = s.check_sat().unwrap();
                s.push().unwrap();
                s.write_str(goal).unwrap();
                let goal_ans = s.check_sat().unwrap();
                s.pop().unwrap();

                match &rp.verdict {
                    Verdict::Verified => {
                        assert_ne!(vac, SmtSolverResponse::Unsat, "{}", file.display());
                        assert_eq!(goal_ans, SmtSolverResponse::Unsat, "{}", file.display());
                    }
                    Verdict::Unreachable { .. } => {
                        assert_eq!(vac, SmtSolverResponse::Unsat, "{}", file.display());
                    }
                    Verdict::GoalFails { .. } => {
                        assert_ne!(vac, SmtSolverResponse::Unsat, "{}", file.display());
                        assert_eq!(goal_ans, SmtSolverResponse::Sat, "{}", file.display());
                    }
                    Verdict::Inconclusive { .. } => {}
                }
                checked += 1;
            }
        }
        assert!(checked > 0, "no pairs to check");
    }

    /// Story 11 — ids in `smt/` match the ids `trace.json` / the HTML show:
    /// `smt/<L>/<R>.smt2` exists for every pair the coverage mode covers, and
    /// `smt/<L>/left.smt2` for every explored left path.
    #[test]
    fn smt_tree_ids_match_the_trace() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions {
                smt_out: SmtOut::All,
                ..DebugOptions::default()
            },
        );
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        assert!(smt.join("base.smt2").exists());
        for lp in &run.left_paths {
            assert!(smt.join(&lp.id).join("left.smt2").exists(), "left #{}", lp.id);
            for rp in &lp.right_paths {
                let rtail = rp.id.rsplit('.').next().unwrap();
                assert!(
                    smt.join(&lp.id).join(format!("{rtail}.smt2")).exists(),
                    "pair #{}",
                    rp.id
                );
            }
        }
    }

    /// Story 11 — `--smt failures` (the default) writes pair files only for
    /// goal-fails / inconclusive pairs; a fully-green run gets `base.smt2` +
    /// `left.smt2`s and no pair files.
    #[test]
    fn smt_failures_covers_only_failing_pairs() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions::default(),
        );
        assert_eq!(run.summary.goal_fails + run.summary.inconclusive, 0);
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        for lp in &run.left_paths {
            for rp in &lp.right_paths {
                let rtail = rp.id.rsplit('.').next().unwrap();
                assert!(
                    !smt.join(&lp.id).join(format!("{rtail}.smt2")).exists(),
                    "no pair file expected for the green pair #{}",
                    rp.id
                );
            }
        }
    }

    /// Story 11 — `--smt deltas`: the per-pair file carries neither the base
    /// frame nor the left path, and `base.smt2 ++ left.smt2 ++ <r>.smt2`
    /// reassembles to the recorded verdict.
    #[test]
    fn smt_deltas_files_are_headerless_and_reassemble() {
        use crate::util::smtsolver::{SmtSolver, SmtSolverBackend, SmtSolverResponse};

        let run = run_in_tmp(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions {
                smt_out: SmtOut::Deltas,
                ..DebugOptions::default()
            },
        );
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        let base = std::fs::read_to_string(smt.join("base.smt2")).unwrap();

        let mut checked = 0usize;
        for lp in &run.left_paths {
            let left = std::fs::read_to_string(smt.join(&lp.id).join("left.smt2")).unwrap();
            assert!(!left.contains("set-logic"), "left.smt2 is always a delta");
            for rp in &lp.right_paths {
                let rtail = rp.id.rsplit('.').next().unwrap();
                let pair =
                    std::fs::read_to_string(smt.join(&lp.id).join(format!("{rtail}.smt2"))).unwrap();
                assert!(
                    !pair.contains("set-logic"),
                    "deltas pair file must not carry the base frame"
                );
                assert!(pair.contains("cat sequential/smt/base.smt2"));

                // Reassemble base ++ left ++ pair-right and re-derive the
                // vacuity answer (the `cat … | cvc5` recipe, in-process).
                let backend = Cvc5LibBackend::new(true, None);
                let mut s = backend.new_smtsolver().unwrap();
                s.write_str(&base).unwrap();
                for line in lp.smt.iter().chain(rp.smt.iter()) {
                    s.write_str(line).unwrap();
                    s.write_str("\n").unwrap();
                }
                let vac = s.check_sat().unwrap();
                if let Verdict::Unreachable { .. } = rp.verdict {
                    assert_eq!(vac, SmtSolverResponse::Unsat);
                } else {
                    assert_ne!(vac, SmtSolverResponse::Unsat);
                }
                checked += 1;
            }
        }
        assert!(checked > 0);
    }

    /// Story 11 — the killer test against the **real `cvc5` binary** (not the
    /// lib backend): an emitted self-contained pair file runs to completion with
    /// a bare `cvc5 <file>` and its second `(check-sat)` matches the recorded
    /// verdict. Ignored by default — needs `cvc5` on `PATH`.
    #[test]
    #[ignore = "needs the cvc5 binary on PATH"]
    fn emitted_pair_file_runs_under_the_cvc5_binary() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions {
                smt_out: SmtOut::All,
                ..DebugOptions::default()
            },
        );
        let smt = std::path::Path::new(&run.out_dir).join("sequential/smt");
        let mut checked = 0usize;
        for lp in &run.left_paths {
            for rp in &lp.right_paths {
                let rtail = rp.id.rsplit('.').next().unwrap();
                let file = smt.join(&lp.id).join(format!("{rtail}.smt2"));
                let out = std::process::Command::new("cvc5")
                    .arg("--lang")
                    .arg("smt2")
                    .arg(&file)
                    .output()
                    .expect("run cvc5");
                let stdout = String::from_utf8_lossy(&out.stdout);
                // First line: vacuity; second: negated goal.
                let answers: Vec<&str> = stdout.lines().take(2).collect();
                assert_eq!(answers.first().copied(), Some("sat"), "vacuity: {stdout}");
                match &rp.verdict {
                    Verdict::Verified => {
                        assert_eq!(answers.get(1).copied(), Some("unsat"), "{}", file.display())
                    }
                    Verdict::GoalFails { .. } => {
                        assert_eq!(answers.get(1).copied(), Some("sat"), "{}", file.display())
                    }
                    _ => {}
                }
                checked += 1;
            }
        }
        assert!(checked > 0);
    }

    /// The epic's primary target, happy path: exits ok, every surviving pair is
    /// `Verified`, and branch pruning did cut the contradictory subtrees (with
    /// pruning the `Unreachable` terminal pairs mostly disappear — they are
    /// removed one level up; `vacuity_runs_with_all_pruning_off` covers the
    /// `Unreachable` verdict itself).
    #[test]
    fn kem_dem_pkgen_same_output_all_green() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions::default(),
        );
        assert_eq!(run.summary.goal_fails, 0, "{}", render_tree(&run));
        assert!(run.is_ok(), "{}", render_tree(&run));
        assert!(run.summary.verified > 0, "{}", render_tree(&run));
        assert_eq!(
            run.summary.verified + run.summary.unreachable,
            run.summary.right_paths
        );
        assert!(
            run.summary.left_pruned_branches + run.summary.right_pruned_branches > 0,
            "expected branch-level pruning to fire: {}",
            render_tree(&run)
        );
    }

    /// `--timeout 1` on a non-trivial claim: a goal check that cannot be decided
    /// in the budget times out to `Inconclusive`, never to `Verified` or a false
    /// `GOAL FAILS`. Run with pruning **off** so the un-pruned shape holds — with
    /// pruning on, the incremental branch context makes even PKENC's goal checks
    /// resolve in well under a millisecond, so nothing stays inconclusive (a good
    /// property, but not what this test is about).
    #[test]
    fn tiny_timeout_yields_inconclusive_never_a_false_pass() {
        let opts = DebugOptions {
            timeout_ms: Some(1),
            ..both_off()
        };
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKENC",
            "same-output",
            opts,
        );
        assert_eq!(run.summary.goal_fails, 0, "{}", render_tree(&run));
        assert!(
            run.summary.inconclusive > 0,
            "with --timeout 1 the real goal checks should be Inconclusive: {}",
            render_tree(&run)
        );
        assert!(!run.is_ok());
        // A timeout is `unknown`, so it is explored, never pruned.
        assert_eq!(run.summary.left_pruned_branches, 0);
        assert_eq!(run.summary.right_pruned_branches, 0);
        assert_eq!(run.summary.left_paths, 6);
        assert_eq!(run.summary.right_paths, 96);
    }

    fn both_off() -> DebugOptions {
        DebugOptions {
            check_left: false,
            check_right: false,
            ..DebugOptions::default()
        }
    }

    /// `--no-check-left --no-check-right` reproduces the un-pruned full
    /// enumeration exactly, and the vacuity check still runs (it is unconditional
    /// as of story 08) so the verdicts are still fully distinguished. Then the
    /// default (both on) prunes the right tree — strictly fewer right paths —
    /// without changing the verdict set: pruning only ever removes pairs that
    /// would have been `Unreachable`.
    #[test]
    fn pruning_shrinks_the_tree_without_changing_verdicts() {
        let base = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKENC",
            "same-output",
            both_off(),
        );
        assert_eq!(base.summary.left_paths, 6, "{}", render_tree(&base));
        assert_eq!(base.summary.right_paths, 96, "{}", render_tree(&base));
        assert_eq!(base.summary.goal_fails, 0);
        assert_eq!(base.summary.verified, 2, "{}", render_tree(&base));
        assert_eq!(base.summary.unreachable, 94, "{}", render_tree(&base));
        assert_eq!(base.summary.left_pruned_branches, 0);
        assert_eq!(base.summary.right_pruned_branches, 0);

        let def = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKENC",
            "same-output",
            DebugOptions::default(),
        );
        assert_eq!(def.summary.goal_fails, 0, "{}", render_tree(&def));
        assert!(
            def.summary.right_paths < base.summary.right_paths,
            "default pruning must yield strictly fewer right paths: {}",
            render_tree(&def)
        );
        assert!(def.summary.right_pruned_branches > 0);
        // every explored pair is still accounted for, and the goal-verified set
        // is unchanged (only unreachable pairs are cut).
        assert_eq!(
            def.summary.verified + def.summary.unreachable,
            def.summary.right_paths
        );
        assert_eq!(def.summary.verified, base.summary.verified);
        assert!(def.summary.unreachable <= base.summary.unreachable);
        assert!(def.is_ok());
    }

    /// The vacuity check is unconditional: even with all early pruning off, a
    /// fixture with an unreachable pair still reports it.
    #[test]
    fn vacuity_runs_with_all_pruning_off() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            both_off(),
        );
        assert_eq!(run.summary.goal_fails, 0, "{}", render_tree(&run));
        assert!(
            run.summary.unreachable > 0,
            "vacuity must still label unreachable pairs: {}",
            render_tree(&run)
        );
        assert!(run.is_ok());
    }

    #[test]
    fn max_paths_stops_early_and_flags_partial() {
        let opts = DebugOptions {
            max_paths: Some(1),
            ..DebugOptions::default()
        };
        let run = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            opts,
        );
        assert!(run.partial());
        assert_eq!(run.stop_reason, StopReason::MaxPaths { limit: 1 });
        assert!(!run.is_ok());
    }

    /// `check_left` (default on) prunes whole left abort paths at their terminal
    /// under `no-abort`, and branch-level under contradictory asserts — without
    /// changing any verdict versus the un-pruned run.
    #[test]
    fn check_left_prunes_without_changing_verdicts() {
        let base = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            both_off(),
        );
        let pruned = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            DebugOptions::default(),
        );
        assert!(
            pruned.summary.left_pruned > 0 || pruned.summary.left_pruned_branches > 0,
            "expected some left pruning under `no-abort`: {}",
            render_tree(&pruned)
        );
        assert_eq!(base.summary.goal_fails, 0);
        assert_eq!(pruned.summary.goal_fails, 0);
        assert_eq!(base.summary.verified, pruned.summary.verified);
    }

    /// Story 09: the observer sees a well-formed event stream —
    /// `Started` → (`LeftPathStarted` → …pairs… → `LeftPathFinished`)* →
    /// `Finished` — with `index` monotonic and `Finished.summary == run.summary`.
    #[test]
    fn observer_sees_a_well_formed_event_stream() {
        let mut obs = RecordingObserver::default();
        let run = run_in_tmp_with(
            "example-projects/hello-world",
            "Proof",
            "UsefulOracle",
            "same-output",
            DebugOptions::default(),
            &mut obs,
            None,
        );

        assert_eq!(obs.events.first().map(String::as_str), Some("Started"));
        assert_eq!(obs.events.last().map(String::as_str), Some("Finished"));

        // Totals is emitted exactly once, right after Started, before any pair.
        assert_eq!(obs.events.get(1).map(String::as_str), Some("Totals"));
        assert_eq!(obs.events.iter().filter(|e| *e == "Totals").count(), 1);
        // Both are syntactic upper bounds: the run reaches no more than promised.
        let (lt, rt) = obs.totals.expect("Totals seen");
        assert!(lt > 0 && rt > 0);
        assert!(lt as usize >= run.summary.left_paths);

        // exactly one Started and one Finished
        assert_eq!(obs.events.iter().filter(|e| *e == "Started").count(), 1);
        assert_eq!(obs.events.iter().filter(|e| *e == "Finished").count(), 1);

        // one LeftPathStarted / LeftPathFinished per left path, indices 1..=n
        let n = run.summary.left_paths;
        assert!(n > 0);
        assert_eq!(obs.left_started, (1..=n).collect::<Vec<_>>());
        assert_eq!(obs.left_finished, (1..=n).collect::<Vec<_>>());

        // every LeftPathStarted is eventually matched by a LeftPathFinished, in
        // order, with only pair-level events (or a prune) in between.
        let mut depth = 0i32;
        for e in &obs.events {
            match e.as_str() {
                "LeftPathStarted" => {
                    assert_eq!(depth, 0, "nested left paths");
                    depth = 1;
                }
                "LeftPathFinished" => {
                    assert_eq!(depth, 1, "LeftPathFinished without a start");
                    depth = 0;
                }
                "PairChecked" | "BranchPruned" | "LeftPathPruned" => {
                    assert_eq!(depth, 1, "pair event outside a left path");
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0);

        assert_eq!(obs.last_summary, Some(run.summary));
        assert_eq!(
            obs.events.iter().filter(|e| *e == "PairChecked").count(),
            run.summary.right_paths
        );
    }

    /// Story 09: a pre-set stop flag makes `explore_paths` bail immediately with
    /// a well-formed, `partial` `DebugRun` and usable artifacts.
    #[test]
    fn stop_flag_bails_with_a_partial_run() {
        let stop = AtomicBool::new(true);
        let mut obs = RecordingObserver::default();
        let run = run_in_tmp_with(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            DebugOptions::default(),
            &mut obs,
            Some(&stop),
        );

        assert!(run.partial(), "{}", render_tree(&run));
        assert_eq!(run.stop_reason, StopReason::Interrupted);
        assert!(!run.is_ok());
        assert!(run.summary.left_paths <= 1);
        // The pre-set flag is caught by `SolverPruner::enter` returning
        // `ExecError::Cancelled`; the driver converted it to `partial` rather
        // than propagating (this call `.unwrap()`s the `Result`) and the
        // solver-stack balance `debug_assert`s in `explore_paths` /
        // `handle_left_path` did not fire.
        // Started + Finished still bracket the (empty) exploration.
        assert_eq!(obs.events.first().map(String::as_str), Some("Started"));
        assert_eq!(obs.events.last().map(String::as_str), Some("Finished"));

        // partial artifacts exist, parse, and carry the stop reason.
        let trace = std::fs::read_to_string(
            std::path::Path::new(&run.out_dir).join("sequential_trace.json"),
        )
        .unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&trace).unwrap();
        assert_eq!(parsed["stop_reason"]["kind"], "interrupted");
        assert!(parsed.get("partial").is_none());
        assert!(std::path::Path::new(&run.out_dir).join("sequential_viewer.html").exists());
        let summary_txt = std::path::Path::new(&run.out_dir).join("sequential_summary.txt");
        assert!(summary_txt.exists());
        assert!(!std::fs::read_to_string(&summary_txt).unwrap().is_empty());
    }

    /// Story 10: a `Ctrl-C` that lands *after* exploration has started (here the
    /// flag is set from inside the observer, on the first `PairChecked`) still
    /// stops cleanly — `SolverPruner::enter` returns `ExecError::Cancelled` on
    /// the next fork, the driver records `partial` without erroring, and the
    /// solver-stack `debug_assert`s hold.
    #[test]
    fn stop_flag_set_mid_sweep_stops_cleanly() {
        struct Tripwire<'a> {
            stop: &'a AtomicBool,
            pairs: usize,
        }
        impl DebugObserver for Tripwire<'_> {
            fn on_event(&mut self, ev: &DebugEvent<'_>) {
                if let DebugEvent::PairChecked { .. } = ev {
                    self.pairs += 1;
                    self.stop.store(true, Ordering::Relaxed);
                }
            }
        }

        let stop = AtomicBool::new(false);
        let mut obs = Tripwire {
            stop: &stop,
            pairs: 0,
        };
        let run = run_in_tmp_with(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            DebugOptions::default(),
            &mut obs,
            Some(&stop),
        );

        assert!(run.partial(), "{}", render_tree(&run));
        assert_eq!(run.stop_reason, StopReason::Interrupted);
        assert!(!run.is_ok());
        // At least one pair was checked before the stop took effect, and the
        // run still produced a well-formed, flushed trace.
        assert!(obs.pairs >= 1);
        let parsed: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("sequential_trace.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(parsed["stop_reason"]["kind"], "interrupted");
        assert_eq!(parsed["schema"], 9);

        // story 17: the summary.txt written by the same (interrupted) flush is
        // the per-left-path tree, ending with the bracketed stop line.
        let summary =
            std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("sequential_summary.txt")).unwrap();
        assert!(!summary.is_empty());
        assert!(summary.starts_with(&render_tree(&run)), "{summary}");
        assert!(summary.starts_with("theorem "), "{summary}");
        assert!(
            summary
                .trim_end()
                .ends_with(&format!(
                    "[STOPPED EARLY (interrupted by Ctrl-C) — {} of {} left paths explored]",
                    run.left_paths.len(),
                    run.left_syntactic
                )),
            "{summary}"
        );
        // one tree block per explored left path; verdict counts from render_tree
        let sm = &run.summary;
        assert_eq!(summary.matches("left path #").count(), run.left_paths.len());
        assert!(
            summary.contains(&format!("{} verified, {} unreachable", sm.verified, sm.unreachable)),
            "{summary}"
        );
    }
}

#[cfg(all(test, feature = "cvc5-lib"))]
mod story19_tests {
    //! Story 19 — all-claim runs. `testdata/story19/deps` is built for it: `AbortDiff` has one
    //! side abort where the other does not, `Branch` has a project-lemma dependency only the
    //! solver can see is false, `Admitted` has an admitted claim.

    use super::*;
    use crate::debug::progress::NopObserver;
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;

    const DEPS: &str = "testdata/story19/deps";

    fn with_project<R>(dir: &str, f: impl FnOnce(&DirectoryProject) -> R) -> R {
        let files = DirectoryFiles::load(std::path::Path::new(dir)).unwrap();
        let proj = DirectoryProject::load(std::path::PathBuf::from(dir), &files).unwrap();
        f(&proj)
    }

    fn run(
        dir: &str,
        theorem: &str,
        step: usize,
        oracle: &str,
        claim: Option<&str>,
        opts: DebugOptions,
    ) -> DebugRun {
        with_project(dir, |proj| {
            let out = tempfile::tempdir().unwrap().into_path();
            run_debug_command(
                proj,
                theorem,
                step,
                oracle,
                claim,
                &opts,
                &Cvc5LibBackend::new(true, opts.timeout_ms),
                Some(out),
                &mut NopObserver,
                None,
            )
            .unwrap()
        })
    }

    fn all(oracle: &str) -> DebugRun {
        run(DEPS, "T", 0, oracle, None, DebugOptions::default())
    }

    fn one(oracle: &str, claim: &str) -> DebugRun {
        run(DEPS, "T", 0, oracle, Some(claim), DebugOptions::default())
    }

    /// Every pair's verdict for `claim`, in path order.
    fn of<'r>(run: &'r DebugRun, claim: &str) -> Vec<&'r Verdict> {
        run.left_paths
            .iter()
            .flat_map(|lp| &lp.right_paths)
            .flat_map(|rp| &rp.claims)
            .filter(|c| c.claim == claim)
            .map(|c| &c.verdict)
            .collect()
    }

    fn dependency_false(dependency: &str) -> Verdict {
        Verdict::Unreachable {
            reason: Unreachability::DependencyFalse {
                dependency: dependency.to_string(),
            },
        }
    }

    fn same(a: &Verdict, b: &Verdict) -> bool {
        serde_json::to_string(a).unwrap() == serde_json::to_string(b).unwrap()
    }

    #[test]
    fn an_all_claim_run_checks_the_whole_obligation_set_in_prove_order() {
        let run = all("Branch");
        assert!(run.all_claims);
        assert_eq!(run.claim, "!all-claims!");
        let names: Vec<_> = run.claims.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(
            names,
            ["equal-aborts", "same-output", "invariant", "needs-positive"]
        );
        let checked: Vec<_> = run.claim_summaries.iter().map(|c| c.claim.as_str()).collect();
        assert_eq!(checked, names);
        assert!(run.is_ok(), "{}", render_tree(&run));
    }

    #[test]
    fn a_pair_where_one_side_aborts_is_unreachable_by_dependency_with_no_solver_call() {
        let run = all("AbortDiff");
        // the left assert holds: both return; it fails: the left aborts, the right returns
        assert_eq!(of(&run, "equal-aborts").len(), 2);
        assert!(matches!(of(&run, "equal-aborts")[1], Verdict::GoalFails { .. }));
        for claim in ["same-output", "invariant"] {
            let verdicts = of(&run, claim);
            assert!(matches!(verdicts[0], Verdict::Verified), "{claim}");
            assert!(
                same(verdicts[1], &dependency_false("no-abort")),
                "{claim}: {}",
                render_tree(&run)
            );
        }
        // three claims on the pair where both return, and only `equal-aborts` — the one whose
        // premise is true — on the pair where the left aborts: deciding `no-abort` cost nothing
        assert_eq!(run.queries.claims, 3 + 1, "{}", render_tree(&run));
        assert!(!run.is_ok());
    }

    #[test]
    fn a_dependency_only_the_solver_can_see_is_false_costs_one_query_after_an_unsat_goal() {
        let run = all("Branch");
        let verdicts = of(&run, "needs-positive");
        assert_eq!(verdicts.len(), 2);
        assert!(matches!(verdicts[0], Verdict::Verified));
        assert!(same(verdicts[1], &dependency_false("positive")), "{}", render_tree(&run));
        // the claim checks: 3 default claims x 2 pairs, and `needs-positive` on each pair, plus
        // the extra dependency queries for it: one on the pair where `positive` holds (asked
        // because the goal was unsat), and on the other pair one to find it false and one to
        // name which dependency it is
        assert_eq!(run.queries.claims, 2 * 3 + 2 + 3, "{}", render_tree(&run));
    }

    #[test]
    fn a_single_claim_run_keeps_its_dependencies_in_the_base_frame() {
        let single = one("Branch", "needs-positive");
        let everything = all("Branch");
        assert!(single.base_frame_smt.contains("(assert (<relation-positive"));
        assert!(!everything.base_frame_smt.contains("(assert (<relation-positive"));
        // with its dependencies asserted up front, the path where `positive` is false is not
        // a pair at all: it is pruned (the frame is unsat there), not reported unreachable
        assert!(single.claim_summaries.is_empty());
        assert_eq!(single.summary.right_paths, 1, "{}", render_tree(&single));
        assert!(single.claims.iter().all(|c| c.name == "needs-positive"));
        assert!(single
            .left_paths
            .iter()
            .flat_map(|lp| &lp.right_paths)
            .all(|rp| rp.claims.is_empty()));
    }

    #[test]
    fn a_single_claim_run_is_the_all_claim_run_with_its_dependencies_moved_to_the_frame() {
        // every verdict of `--claim C` is what the all-claim run says about C, except that a
        // pair `C`'s dependencies make infeasible is not enumerated at all
        for oracle in ["Branch", "AbortDiff", "AbortBoth", "Admitted"] {
            let everything = all(oracle);
            for info in everything.claims.iter().filter(|c| !c.admitted) {
                let single = one(oracle, &info.name);
                let failures_of = |run: &DebugRun| run.summary.goal_fails;
                let all_fails = of(&everything, &info.name)
                    .iter()
                    .filter(|v| matches!(v, Verdict::GoalFails { .. }))
                    .count();
                assert_eq!(failures_of(&single), all_fails, "{oracle} {}", info.name);
            }
        }
    }

    #[test]
    fn the_exploration_is_paid_once_however_many_claims_there_are() {
        // `equal-aborts` has no dependencies, so its single-claim frame is the all-claim one:
        // the same exploration, the same pruning, the same vacuity checks
        for (dir, theorem, oracle) in [
            (DEPS, "T", "Branch"),
            (DEPS, "T", "AbortDiff"),
            ("example-projects/kem-dem/kem-dem-cca-ssp", "kem_dem_cca_ssp", "PKDEC"),
        ] {
            let everything = run(dir, theorem, 0, oracle, None, DebugOptions::default());
            let narrow = run(dir, theorem, 0, oracle, Some("equal-aborts"), DebugOptions::default());
            assert_eq!(
                everything.queries.exploration, narrow.queries.exploration,
                "{oracle}: the exploration must not scale with the claim count"
            );
            assert!(everything.queries.claims > narrow.queries.claims, "{oracle}");
        }
    }

    #[test]
    fn admitted_claims_are_listed_and_never_checked() {
        let run = all("Admitted");
        let skipped = run.claims.iter().find(|c| c.name == "skipped").unwrap();
        assert!(skipped.admitted);
        assert!(of(&run, "skipped").is_empty());
        assert!(run.claim_summaries.iter().all(|c| c.claim != "skipped"));
        assert!(!run.admitted, "the other claims of the oracle are not");
        assert!(render_tree(&run).contains("admitted"), "{}", render_tree(&run));
    }

    #[test]
    fn first_failure_per_claim_stops_checking_a_claim_after_its_first_goal_fails() {
        let dir = "testdata/lockstep/rules";
        let everything = run(dir, "T", 0, "Split", None, DebugOptions::default());
        let fails = |run: &DebugRun| {
            run.claim_summaries
                .iter()
                .find(|c| c.claim == "same-output")
                .unwrap()
                .clone()
        };
        assert_eq!(fails(&everything).goal_fails, 2, "the two mixed combinations");
        assert_eq!(fails(&everything).skipped, 0);

        let first_only = run(
            dir,
            "T",
            0,
            "Split",
            None,
            DebugOptions {
                first_failure_per_claim: true,
                ..DebugOptions::default()
            },
        );
        let f = fails(&first_only);
        assert_eq!(f.goal_fails, 1);
        assert!(f.skipped >= 1, "{f:?}");
        assert!(!first_only.is_ok());
    }

    #[test]
    fn both_strategies_write_into_one_directory_and_neither_wipes_the_other() {
        use crate::debug::lockstep_run::{run_lockstep_domino, LockstepDebugOptions};
        with_project(DEPS, |proj| {
            let out = tempfile::tempdir().unwrap().into_path();
            let seq = run_debug_command(
                proj, "T", 0, "Branch", None, &DebugOptions::default(),
                &Cvc5LibBackend::new(true, None), Some(out.clone()), &mut NopObserver, None,
            )
            .unwrap();
            let lock = run_lockstep_domino(
                proj, "T", 0, "Branch", None, &LockstepDebugOptions::default(),
                &Cvc5LibBackend::new(true, None), Some(out.clone()), &mut NopObserver, None,
            )
            .unwrap();
            assert_eq!(seq.out_dir, lock.meta.out_dir);
            for file in [
                "inlined.txt",
                "sequential_viewer.html",
                "sequential_trace.json",
                "sequential_summary.txt",
                "lockstep_viewer.html",
                "lockstep_trace.json",
                "lockstep_summary.txt",
            ] {
                assert!(out.join(file).is_file(), "{file}");
            }
            for dir in ["sequential/models", "lockstep/models"] {
                assert!(out.join(dir).is_dir(), "{dir}");
            }
            // no file of either is called by the name both would want
            for plain in ["index.html", "trace.json", "summary.txt", "models", "smt"] {
                assert!(!out.join(plain).exists(), "{plain}");
            }
            let seq_summary = std::fs::read_to_string(out.join("sequential_summary.txt")).unwrap();
            let lock_summary = std::fs::read_to_string(out.join("lockstep_summary.txt")).unwrap();
            assert!(seq_summary.contains("\nstrategy sequential\n"), "{seq_summary}");
            assert!(lock_summary.contains("\nstrategy lockstep\n"), "{lock_summary}");
            assert!(crate::debug::report::render_summary(&seq).contains("strategy      sequential\n"));
            assert!(crate::debug::lockstep_report::render_summary(&lock)
                .contains("strategy      lockstep\n"));
            // running the sequential one again leaves the lockstep files as they were
            let before = std::fs::read(out.join("lockstep_trace.json")).unwrap();
            run_debug_command(
                proj, "T", 0, "Branch", None, &DebugOptions::default(),
                &Cvc5LibBackend::new(true, None), Some(out.clone()), &mut NopObserver, None,
            )
            .unwrap();
            assert_eq!(before, std::fs::read(out.join("lockstep_trace.json")).unwrap());
        });
    }

    /// A `TheoremUI` that says nothing: `Project::prove` installs a global logger, which a
    /// test binary can do once.
    struct Silent;

    impl crate::ui::TheoremUI for Silent {
        fn println(&self, _: &str) -> std::io::Result<()> {
            Ok(())
        }
        fn start_theorem(&mut self, _: &str, _: u64) {}
        fn finish_theorem(&mut self, _: &str) {}
        fn start_proofstep(&mut self, _: &str, _: &str) {}
        fn proofstep_is_reduction(&mut self, _: &str, _: &str) {}
        fn proofstep_set_claim_groups_count(&mut self, _: &str, _: &str, _: u64) {}
        fn finish_proofstep(&mut self, _: &str, _: &str) {}
        fn start_claim_group(&mut self, _: &str, _: &str, _: &str, _: u64) {}
        fn finish_claim_group(&mut self, _: &str, _: &str, _: &str) {}
        fn start_claim(&mut self, _: &str, _: &str, _: &str, _: &str) {}
        fn finish_claim(&mut self, _: &str, _: &str, _: &str, _: &str) {}
    }

    /// What `domino prove --proof T --proofstep N --oracle O --claim C` concludes.
    fn prove_says_ok(
        proj: &DirectoryProject,
        theorem: &str,
        step: usize,
        oracle: &str,
        claim: &str,
        backend: &Cvc5LibBackend,
    ) -> bool {
        use crate::gamehops::equivalence::verify_fn::EquivalenceSmtDriver;
        let theorem = proj.get_theorem(theorem).unwrap();
        let (transformed, auxs) = EquivalenceTransform.transform_theorem(theorem).unwrap();
        let eq = equivalence_of(theorem, step).unwrap();
        let mut eqctx = EquivalenceContext::new(eq, &transformed, &auxs);
        eqctx.load_invariants(proj).unwrap();
        let mut driver = EquivalenceSmtDriver::new(
            &eqctx, proj, backend, false, Some(oracle), Some(claim), 1, false, false,
        );
        driver.verify(&mut Silent).is_ok()
    }

    /// `domino prove` decides each claim of an oracle on its own; an all-claim run must reach
    /// the same verdict for it: `prove` succeeds exactly when no pair fails the claim.
    #[test]
    fn an_all_claim_run_agrees_with_prove_claim_by_claim() {
        use crate::debug::sweep;
        use crate::project::Project as _;

        let mut compared = 0usize;
        for (dir, theorem) in [
            ("example-projects/hello-world", "Proof"),
            ("example-projects/simple-KEM-example", "KEM_Proof"),
            ("test-projects/test-splitinvoke", ""),
            ("testdata/lockstep/rules", "T"),
            (DEPS, "T"),
        ] {
            with_project(dir, |proj| {
                let theorem = if theorem.is_empty() {
                    proj.theorems().next().unwrap().to_string()
                } else {
                    theorem.to_string()
                };
                let plan = sweep::plan(proj, Some(&theorem), None, None).unwrap();
                for target in &plan.targets {
                    let out = tempfile::tempdir().unwrap().into_path();
                    let opts = DebugOptions::default();
                    let backend = Cvc5LibBackend::new(true, None);
                    let run = run_debug_command(
                        proj, &target.theorem, target.proofstep, &target.oracle, None, &opts,
                        &backend, Some(out), &mut NopObserver, None,
                    )
                    .unwrap();
                    assert_eq!(run.stop_reason, StopReason::Completed);
                    for c in &run.claim_summaries {
                        assert_eq!(
                            c.inconclusive, 0,
                            "{dir} {}: an undecided query breaks the comparison",
                            target.oracle
                        );
                        let proved = prove_says_ok(
                            proj,
                            &target.theorem,
                            target.proofstep,
                            &target.oracle,
                            &c.claim,
                            &backend,
                        );
                        assert_eq!(
                            proved,
                            c.goal_fails == 0,
                            "{dir} {} {}: prove says {proved}, the all-claim run found {} failing pairs",
                            target.oracle,
                            c.claim,
                            c.goal_fails
                        );
                        compared += 1;
                    }
                }
            });
        }
        assert!(compared >= 20, "only {compared} claims were compared");
    }
}

