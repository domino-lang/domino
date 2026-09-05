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

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use serde_derive::Serialize;

use crate::debug::exec::{
    execute_streaming_with_oracle, BranchOracle, BranchQuery, ExecError, Feasibility, Side, Step,
    Terminal, TerminalPath,
};
use crate::debug::ir::{
    count_terminals, inline_oracle, InlineError, InlinedOracle, Label, Listing, SiteInfo, SiteKind,
};
use crate::debug::progress::{DebugEvent, DebugObserver, SharedObserver};
use crate::debug::render;
use crate::debug::report;
use crate::debug::smtout::{SmtOut, SmtWriter};
use crate::gamehops::GameHop;
use crate::project::Project;
use crate::theorem::{Claim, GameInstance};
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
pub const TRACE_SCHEMA: u32 = 7;

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
    pub theorem: String,
    pub proofstep: usize,
    pub left_game: String,
    pub right_game: String,
    pub oracle: String,
    pub claim: String,
    /// The claim is admitted — there is nothing to check.
    pub admitted: bool,
    /// The output directory. Absolute — **skipped** in `trace.json` so two runs
    /// on the same project produce byte-identical output.
    #[serde(skip)]
    pub out_dir: String,
    /// The options this run was launched with.
    pub options: OptionsView,
    /// The base declarations asserted once at solver level 0, rendered. This is
    /// also the head of `transcript.smt2` up to the first `(push 1)`; kept here
    /// so `index.html` is self-contained. Empty for an admitted claim.
    pub base_frame_smt: String,
    /// The negated claim goal — `(assert (not …))` — checked at every (left,
    /// right) terminal pair after the vacuity check. One per run: it depends on
    /// the claim and the oracle, not on the path. Empty for an admitted claim.
    /// The viewer's `Claim assertion` section renders it (story 13).
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
    /// Number of syntactic left terminals (`ir::count_terminals`) — the "of N"
    /// denominator in `summary.txt`'s left-path line. `0` for an admitted claim.
    /// Deterministic; safe in `trace.json`.
    pub left_syntactic: u64,
    /// Why exploration ended (story 12). Replaces the old `partial: bool` — kept
    /// at the same field position so the serialised order stays predictable.
    /// `Completed` unless `--max-paths` fired or a `Ctrl-C` landed.
    pub stop_reason: StopReason,
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

fn sites_view(listing: &Listing) -> BTreeMap<Label, SiteView> {
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
    /// Line ranges of the right listing this path executed (story 16), same
    /// shape as [`LeftPath::lines`].
    pub lines: Vec<[usize; 2]>,
    pub verdict: Verdict,
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
    /// Vacuity check `unsat` — the pair cannot happen. **Not** the same as
    /// `Verified`.
    Unreachable,
    /// Goal check `sat` — the claim fails; `model` is the written model file
    /// (relative to the output directory).
    GoalFails { model: String },
    /// Goal check `unknown` / timed out.
    Inconclusive { model: Option<String> },
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

/// Run `domino debug` for one claim and return the (serialisable) run.
///
/// Writes `transcript.smt2`, `inlined.txt` and any model files under `out`
/// (defaulting to `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`).
#[allow(clippy::too_many_arguments)]
pub fn run_debug_command<P, B>(
    project: &P,
    req_proof: &str,
    req_proofstep: usize,
    oracle: &str,
    claim_name: &str,
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
    // Wall-clock, for `summary.txt` only — never enters `DebugRun` /
    // `trace.json` (story 07 determinism).
    let started = Instant::now();

    let theorem = project
        .get_theorem(req_proof)
        .ok_or_else(|| DebugError::TheoremNotFound {
            name: req_proof.to_string(),
        })?;

    let n_hops = theorem.game_hops.len();
    let hop = theorem
        .game_hops
        .get(req_proofstep)
        .ok_or(DebugError::ProofstepOutOfRange {
            index: req_proofstep,
            len: n_hops,
        })?;
    let eq = match hop {
        GameHop::Equivalence(eq) => eq,
        GameHop::Hybrid(hyb) => hyb.equivalence(),
        GameHop::Reduction(_) => {
            return Err(DebugError::ProofstepNotEquivalence {
                index: req_proofstep,
                kind: "reduction",
            })
        }
        GameHop::Conjecture(_) => {
            return Err(DebugError::ProofstepNotEquivalence {
                index: req_proofstep,
                kind: "conjecture",
            })
        }
    };

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

    // Resolve the claim: the user-written proof tree for this oracle, plus the
    // generated package/game invariant claims (same set `prove` checks).
    let mut claims = eq.proof_tree_by_oracle_name(oracle);
    claims.extend(eqctx.generate_game_or_package_invariant_claims());
    let claim = claims
        .iter()
        .find(|claim| claim.name() == claim_name)
        .cloned()
        .ok_or_else(|| DebugError::ClaimNotFound {
            claim: claim_name.to_string(),
            available: claims.iter().map(|c| c.name().to_string()).collect(),
        })?;

    observer.on_event(&DebugEvent::Started {
        oracle,
        claim: claim_name,
        admitted: claim.is_admitted(),
    });

    let left_inl = inline_oracle(left_inst, oracle)?;
    let right_inl = inline_oracle(right_inst, oracle)?;

    // Solver-free syntactic path counts — upper bounds the progress display
    // shows as `k/N` and the "of N syntactic" denominator in `summary.txt`.
    // Skipped for an admitted claim (nothing between `Started { admitted }` and
    // `Finished`).
    let (left_syntactic, right_syntactic) = if claim.is_admitted() {
        (0, 0)
    } else {
        (count_terminals(&left_inl), count_terminals(&right_inl))
    };
    if !claim.is_admitted() {
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
        path.push("_build/debug");
        path.push(eq.theorem_name());
        path.push(format!("{}-{}", eq.left_name(), eq.right_name()));
        path.push(oracle);
        path.push(claim_name);
        path
    });
    std::fs::create_dir_all(&out_dir)?;
    std::fs::create_dir_all(out_dir.join("models"))?;

    let mut run = DebugRun {
        schema: TRACE_SCHEMA,
        theorem: eq.theorem_name().to_string(),
        proofstep: req_proofstep,
        left_game: eq.left_name().to_string(),
        right_game: eq.right_name().to_string(),
        oracle: oracle.to_string(),
        claim: claim_name.to_string(),
        admitted: claim.is_admitted(),
        out_dir: out_dir.display().to_string(),
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
        left_syntactic,
        stop_reason: StopReason::Completed,
    };

    if !claim.is_admitted() {
        let base = base_frame(&eqctx, oracle, &claim);
        run.base_frame_smt = base
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        // Story 11: the per-path `smt/` tree is the primary artifact. The
        // monolithic `transcript.smt2` is opt-in (`--transcript`) — it doubles
        // every byte the driver sends and is only useful for debugging the
        // driver itself.
        let smt_writer = SmtWriter::new(&out_dir, opts.smt_out, &run)?;
        // Computed once here (story 11): the negated claim goal. `check_pair`
        // used to re-derive it per pair; the `smt/` files embed its text.
        let goal_negated = eqctx.emit_claim_goal_negated(&claim, oracle);
        let goal_smt = goal_negated.to_string();
        // Story 13: hoist the same text onto the run so `trace.json` /
        // `index.html` show the exact assertion the solver was asked about.
        run.goal_smt = goal_smt.clone();

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

        // The left `BranchOracle` and the terminal handler both need the solver,
        // at different (never overlapping) points of the executor's DFS — hence
        // the `RefCell`. See `SolverPruner`.
        let solver = RefCell::new(solver);
        explore_paths(
            &solver, &left_inl, &right_inl, left_inst, right_inst, left_si, right_si, opts,
            &out_dir, &observer, stop, &smt_writer, &goal_negated, &goal_smt, started, &mut run,
        )?;

        solver.into_inner().close();
    }

    std::fs::write(
        out_dir.join("inlined.txt"),
        render::side_by_side(&run.left_listing, &run.right_listing),
    )?;
    report::flush(&run, started.elapsed(), &out_dir)?;

    observer.borrow_mut().on_event(&DebugEvent::Finished {
        summary: run.summary,
        stop_reason: run.stop_reason,
    });

    Ok(run)
}

// ---------------------------------------------------------------------------
// Base frame
// ---------------------------------------------------------------------------

/// The declarations asserted once at solver level 0. Same order and content as
/// `verify_fn.rs`, with `emit_constant_declarations` narrowed to `Some(oracle)`
/// (story 04) and the claim assumptions split out and asserted positively.
fn base_frame<'a>(
    eqctx: &'a EquivalenceContext<'a>,
    oracle: &str,
    claim: &Claim,
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
    base.extend(eqctx.emit_claim_assumptions(claim, oracle));
    base
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
    goal_negated: &SmtExpr,
    goal_smt: &str,
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
                goal_negated,
                goal_smt,
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
                    observer.borrow_mut().on_event(&DebugEvent::LeftPathFinished {
                        index,
                        running: run.summary,
                    });
                    if let Err(e) = report::flush(run, started.elapsed(), out_dir) {
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
    goal_negated: &SmtExpr,
    goal_smt: &str,
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
        !matches!(solver.borrow_mut().check_sat()?, SmtSolverResponse::Unsat)
    } else {
        true
    };

    let mut left_view = LeftPath {
        id: lid.to_string(),
        steps: steps_view(left_listing, &lp.steps),
        terminal: terminal_view(left_listing, &lp.terminal),
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
                    goal_negated,
                    out_dir,
                    &right_inl.listing,
                    &rid,
                    rp,
                    observer,
                ) {
                    Ok(rv) => {
                        // Story 11: `smt/<lid>/<r>.smt2` for the pairs the
                        // coverage mode wants (a no-op otherwise).
                        if let Err(e) = smt_writer.write_pair(lid, left_view, &rv, goal_smt) {
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
    goal_negated: &SmtExpr,
    out_dir: &Path,
    right_listing: &Listing,
    rid: &str,
    rp: &TerminalPath,
    observer: &SharedObserver<'o>,
) -> Result<RightPath, DebugError> {
    let (verdict, model_smt) = {
        let mut s = solver.borrow_mut();
        s.push()?;
        write_path_delta(&mut *s, rp)?;
        let t0 = Instant::now();
        let (verdict, model_smt) = check_pair(&mut *s, goal_negated, rid, out_dir)?;
        s.pop()?;
        drop(s);
        observer.borrow_mut().on_event(&DebugEvent::PairChecked {
            id: rid,
            verdict: &verdict,
            elapsed: t0.elapsed(),
        });
        (verdict, model_smt)
    };
    Ok(RightPath {
        id: rid.to_string(),
        steps: steps_view(right_listing, &rp.steps),
        terminal: terminal_view(right_listing, &rp.terminal),
        lines: lines_view(&rp.lines),
        verdict,
        model_smt,
        smt: render_path_smt(rp),
    })
}

/// At a (left, right) terminal pair: **unconditional** vacuity, then the negated
/// goal. Returns the verdict and, for `goal-fails` / `inconclusive`, the model
/// text (also written to `models/<rid>.smt2`).
fn check_pair<S: SmtSolver>(
    solver: &mut S,
    goal_negated: &SmtExpr,
    rid: &str,
    out_dir: &Path,
) -> Result<(Verdict, Option<String>), DebugError> {
    // Vacuity (overview §3) — UNCONDITIONAL as of story 08. `unsat` here means
    // the pair cannot happen; it is **not** the same as `Verified`.
    if matches!(solver.check_sat()?, SmtSolverResponse::Unsat) {
        return Ok((Verdict::Unreachable, None));
    }

    solver.push()?;
    // Story 11: `goal_negated` is `eqctx.emit_claim_goal_negated(claim, oracle)`,
    // computed once in `run_debug_command` (its text also lands in `smt/`).
    solver.write_smt(goal_negated.clone())?;
    let outcome = match solver.check_sat()? {
        SmtSolverResponse::Unsat => (Verdict::Verified, None),
        SmtSolverResponse::Sat => {
            let (rel, text) = write_model(solver, out_dir, rid)?;
            (Verdict::GoalFails { model: rel }, Some(text))
        }
        SmtSolverResponse::Unknown => match write_model(solver, out_dir, rid) {
            Ok((rel, text)) => (Verdict::Inconclusive { model: Some(rel) }, Some(text)),
            Err(_) => (Verdict::Inconclusive { model: None }, None),
        },
    };
    solver.pop()?;
    Ok(outcome)
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
    ) -> Self {
        Self {
            solver,
            enabled,
            listing,
            id_prefix,
            observer,
            side,
            stop,
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

/// Writes the current model to `models/<rid>.smt2` and returns
/// `(relative path, model text)`.
fn write_model<S: SmtSolver>(
    solver: &mut S,
    out_dir: &Path,
    rid: &str,
) -> Result<(String, String), DebugError> {
    let (model, _) = solver.get_model()?;
    let rel = format!("models/{rid}.smt2");
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

fn steps_view(listing: &Listing, steps: &[Step]) -> Vec<StepView> {
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

fn terminal_view(listing: &Listing, terminal: &Terminal) -> TerminalView {
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
fn lines_view(lines: &[(Label, Label)]) -> Vec<[usize; 2]> {
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
                Verdict::Unreachable => summary.unreachable += 1,
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

/// The text tree printed to stdout (the format agreed with the project owner).
pub fn render_tree(run: &DebugRun) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();

    let _ = writeln!(
        out,
        "theorem {}, proofstep {} ({} == {})",
        run.theorem, run.proofstep, run.left_game, run.right_game
    );
    let _ = writeln!(out, "oracle {}, claim {}", run.oracle, run.claim);

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
            let _ = writeln!(
                out,
                "    #{}  {}{}{}   {}",
                rp.id,
                steps,
                sep,
                terminal,
                render_verdict(&rp.verdict)
            );
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

fn render_verdict(verdict: &Verdict) -> String {
    match verdict {
        Verdict::Verified => "[unsat: ok]".to_string(),
        Verdict::Unreachable => "[unsat: unreachable]".to_string(),
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
                proj, theorem, 0, oracle, claim, &opts, &backend, Some(out), observer, stop,
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
            &std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("trace.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(parsed["schema"], 7);
        assert_eq!(parsed["goal_smt"], run.goal_smt);
    }

    /// Story 13: an admitted claim checks nothing, so `goal_smt` stays empty.
    #[test]
    fn goal_smt_is_empty_for_an_admitted_claim() {
        let run = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKDEC",
            "lemma-kem-correctness",
            DebugOptions::default(),
        );
        assert!(run.admitted);
        assert!(run.goal_smt.is_empty());
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
            !std::path::Path::new(&run.out_dir).join("transcript.smt2").exists(),
            "transcript.smt2 must not be written without --transcript"
        );
        // The `smt/` tree is the default artifact: base frame + one delta per
        // explored left path.
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
            std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("transcript.smt2"))
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
        assert!(!std::path::Path::new(&run.out_dir).join("smt").exists());
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
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
                    Verdict::Unreachable => {
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
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
                assert!(pair.contains("cat smt/base.smt2"));

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
                if let Verdict::Unreachable = rp.verdict {
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
        let smt = std::path::Path::new(&run.out_dir).join("smt");
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
            std::path::Path::new(&run.out_dir).join("trace.json"),
        )
        .unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&trace).unwrap();
        assert_eq!(parsed["stop_reason"]["kind"], "interrupted");
        assert!(parsed.get("partial").is_none());
        assert!(std::path::Path::new(&run.out_dir).join("index.html").exists());
        assert!(std::path::Path::new(&run.out_dir).join("summary.txt").exists());
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
            &std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("trace.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(parsed["stop_reason"]["kind"], "interrupted");
        assert_eq!(parsed["schema"], 7);

        // story 12: the summary.txt written by the same (interrupted) flush
        // agrees with trace.json on the verdict + path counts.
        let summary =
            std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("summary.txt")).unwrap();
        assert!(summary.contains("STOPPED EARLY (interrupted by Ctrl-C)"), "{summary}");
        let sm = &run.summary;
        assert!(summary.contains(&format!("  verified      {}\n", sm.verified)), "{summary}");
        assert!(summary.contains(&format!("  GOAL FAILS    {}\n", sm.goal_fails)), "{summary}");
        assert!(summary.contains(&format!("  {:<13}{} checked\n", "pairs", sm.right_paths)), "{summary}");
    }
}
