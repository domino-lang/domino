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
//! ## Branch pruning vs. what story 05 exposes
//!
//! Story 05's executor has no branch-point callback — it hands back completed
//! [`TerminalPath`]s only. The finest pruning available on that API is therefore
//! *per path*, which is exactly the vacuity check the overview already mandates at
//! every terminal pair. So:
//!
//! - **Vacuity always runs** and distinguishes [`Verdict::Unreachable`] from
//!   [`Verdict::Verified`] — this is a first-class feature, not an optimisation.
//! - `--check-left` adds a per-left-path reachability pre-check; an `unsat` left
//!   path is pruned (recorded, not explored). Changes no verdict, since a pruned
//!   left path's pairs would all have been `Unreachable`.
//! - `--no-check-right` *skips* the vacuity check and runs the goal check on every
//!   right path. It never changes the set of `GOAL FAILS` (an `unsat` context
//!   cannot make `(not goal)` `sat`), only whether unreachable pairs are labelled
//!   `Unreachable` or fall through to `Verified`. It is a diagnostic escape hatch.
//!
//! Only `unsat` ever prunes. `unknown` and timeouts are always explored.

use std::collections::BTreeMap;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};

use serde_derive::Serialize;

use crate::debug::exec::{execute_streaming, ExecError, Side, Step, Terminal, TerminalPath};
use crate::debug::ir::{
    inline_oracle, InlineError, InlinedOracle, Label, Listing, SiteInfo, SiteKind,
};
use crate::debug::render;
use crate::debug::report;
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
    /// Ask the solver which branches of the LEFT oracle are reachable and prune
    /// the `unsat` ones. Default off (explore all).
    pub check_left: bool,
    /// Run the reachability/vacuity check on the RIGHT side (distinguishes
    /// `Unreachable` from `Verified`). Default on.
    pub check_right: bool,
    /// Per-query solver timeout in milliseconds (cvc5 `tlimit-per`). A timeout
    /// counts as `unknown` — explored, never pruned.
    pub timeout_ms: Option<u64>,
    /// Give up after this many explored paths (left paths + right paths per left
    /// path).
    pub max_paths: usize,
}

impl Default for DebugOptions {
    fn default() -> Self {
        Self {
            check_left: false,
            check_right: true,
            timeout_ms: None,
            max_paths: 1000,
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
pub const TRACE_SCHEMA: u32 = 1;

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
    /// The left game instance's inlined listing (line `n` == `Label` `n`).
    pub left_listing: String,
    /// The right game instance's inlined listing (numbered independently).
    pub right_listing: String,
    /// Per-label metadata for the left listing (branch/assert/return/... sites).
    pub left_sites: BTreeMap<Label, SiteView>,
    /// Per-label metadata for the right listing.
    pub right_sites: BTreeMap<Label, SiteView>,
    pub left_paths: Vec<LeftPath>,
    pub summary: Summary,
    /// Exploration stopped early (`--max-paths` or an executor cap). Results are
    /// partial.
    pub partial: bool,
}

/// The CLI knobs, in a shape that serialises cleanly into `trace.json`.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct OptionsView {
    pub check_left: bool,
    pub check_right: bool,
    pub timeout_ms: Option<u64>,
    pub max_paths: usize,
}

impl From<&DebugOptions> for OptionsView {
    fn from(o: &DebugOptions) -> Self {
        Self {
            check_left: o.check_left,
            check_right: o.check_right,
            timeout_ms: o.timeout_ms,
            max_paths: o.max_paths,
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
    /// `false` if `--check-left` proved this path unreachable and pruned it.
    pub reachable: bool,
    /// The exact SMT asserted for this path (`decls` ++ `constraints` ++
    /// `return_constraint`), rendered.
    pub smt: Vec<String>,
    pub right_paths: Vec<RightPath>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RightPath {
    /// `"1.1"`, `"1.2"`, … Rendered `#1.1`.
    pub id: String,
    pub steps: Vec<StepView>,
    pub terminal: TerminalView,
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

#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct Summary {
    pub left_paths: usize,
    pub left_pruned: usize,
    pub right_paths: usize,
    pub verified: usize,
    pub unreachable: usize,
    pub goal_fails: usize,
    pub inconclusive: usize,
}

impl DebugRun {
    /// Every explored pair is `Verified` or `Unreachable` and exploration
    /// finished. This is the process exit-code criterion.
    pub fn is_ok(&self) -> bool {
        !self.partial && self.summary.goal_fails == 0 && self.summary.inconclusive == 0
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
) -> Result<DebugRun, DebugError>
where
    P: Project,
    B: SmtSolverBackend,
{
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

    let left_inl = inline_oracle(left_inst, oracle)?;
    let right_inl = inline_oracle(right_inst, oracle)?;

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
        left_listing: left_inl.listing.text.clone(),
        right_listing: right_inl.listing.text.clone(),
        left_sites: sites_view(&left_inl.listing),
        right_sites: sites_view(&right_inl.listing),
        left_paths: Vec::new(),
        summary: Summary::default(),
        partial: false,
    };

    if !claim.is_admitted() {
        let base = base_frame(&eqctx, oracle, &claim);
        run.base_frame_smt = base
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        let transcript = std::fs::File::create(out_dir.join("transcript.smt2"))?;
        let mut solver = backend.new_smtsolver_with_transcript(transcript)?;
        if let Some(ms) = opts.timeout_ms {
            solver.set_option("tlimit-per", &ms.to_string())?;
        }
        for entry in &base {
            solver.write_smt(entry.clone())?;
        }

        explore_paths(
            &eqctx, &mut solver, oracle, &claim, &left_inl, &right_inl, left_inst, right_inst,
            left_si, right_si, opts, &out_dir, &mut run,
        )?;

        solver.close();
    }

    std::fs::write(
        out_dir.join("inlined.txt"),
        render::side_by_side(&run.left_listing, &run.right_listing),
    )?;
    report::write_trace_json(&run, &out_dir)?;
    report::write_html(&run, &out_dir)?;

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
fn explore_paths<S: SmtSolver>(
    eqctx: &EquivalenceContext<'_>,
    solver: &mut S,
    oracle: &str,
    claim: &Claim,
    left_inl: &InlinedOracle,
    right_inl: &InlinedOracle,
    left_inst: &GameInstance,
    right_inst: &GameInstance,
    left_si: &SampleInfo,
    right_si: &SampleInfo,
    opts: &DebugOptions,
    out_dir: &Path,
    run: &mut DebugRun,
) -> Result<(), DebugError> {
    let (left_paths, left_capped) =
        collect_paths(left_inl, left_inst, left_si, Side::Left, opts.max_paths)?;
    if left_capped {
        run.partial = true;
    }

    let mut explored = 0usize;

    'left: for (i, lp) in left_paths.iter().enumerate() {
        explored += 1;
        if explored > opts.max_paths {
            run.partial = true;
            break;
        }
        let lid = format!("{}", i + 1);

        solver.push()?;
        write_path(solver, lp)?;

        let reachable = if opts.check_left {
            !matches!(solver.check_sat()?, SmtSolverResponse::Unsat)
        } else {
            true
        };

        let mut left_view = LeftPath {
            id: lid.clone(),
            steps: steps_view(&left_inl.listing, &lp.steps),
            terminal: terminal_view(&left_inl.listing, &lp.terminal),
            reachable,
            smt: render_path_smt(lp),
            right_paths: Vec::new(),
        };

        if reachable {
            let (right_paths, right_capped) =
                collect_paths(right_inl, right_inst, right_si, Side::Right, opts.max_paths)?;
            if right_capped {
                run.partial = true;
            }

            for (j, rp) in right_paths.iter().enumerate() {
                explored += 1;
                if explored > opts.max_paths {
                    run.partial = true;
                    solver.pop()?;
                    run.left_paths.push(left_view);
                    break 'left;
                }
                let rid = format!("{}.{}", lid, j + 1);

                solver.push()?;
                write_path(solver, rp)?;
                let (verdict, model_smt) =
                    check_pair(solver, eqctx, claim, oracle, &rid, opts, out_dir)?;
                solver.pop()?;

                left_view.right_paths.push(RightPath {
                    id: rid,
                    steps: steps_view(&right_inl.listing, &rp.steps),
                    terminal: terminal_view(&right_inl.listing, &rp.terminal),
                    verdict,
                    model_smt,
                    smt: render_path_smt(rp),
                });
            }
        }

        solver.pop()?;
        run.left_paths.push(left_view);
    }

    run.summary = summarize(&run.left_paths);
    Ok(())
}

/// At a (left, right) terminal pair: vacuity, then the negated goal. Returns the
/// verdict and, for `goal-fails` / `inconclusive`, the model text (also written
/// to `models/<rid>.smt2`).
fn check_pair<S: SmtSolver>(
    solver: &mut S,
    eqctx: &EquivalenceContext<'_>,
    claim: &Claim,
    oracle: &str,
    rid: &str,
    opts: &DebugOptions,
    out_dir: &Path,
) -> Result<(Verdict, Option<String>), DebugError> {
    // Vacuity (overview §3). Skipped only with `--no-check-right`.
    if opts.check_right && matches!(solver.check_sat()?, SmtSolverResponse::Unsat) {
        return Ok((Verdict::Unreachable, None));
    }

    solver.push()?;
    solver.write_smt(eqctx.emit_claim_goal_negated(claim, oracle))?;
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

fn write_path<S: SmtSolver>(solver: &mut S, path: &TerminalPath) -> Result<(), DebugError> {
    for entry in &path.decls {
        solver.write_smt(entry.clone())?;
    }
    for entry in &path.constraints {
        solver.write_smt(entry.clone())?;
    }
    solver.write_smt(path.return_constraint.clone())?;
    Ok(())
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
fn collect_paths(
    inl: &InlinedOracle,
    inst: &GameInstance,
    sample_info: &SampleInfo,
    side: Side,
    cap: usize,
) -> Result<(Vec<TerminalPath>, bool), ExecError> {
    let mut paths = Vec::new();
    let mut capped = false;
    execute_streaming(inl, inst, sample_info, side, None, &mut |path| {
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

fn render_path_smt(path: &TerminalPath) -> Vec<String> {
    path.decls
        .iter()
        .chain(&path.constraints)
        .chain(std::iter::once(&path.return_constraint))
        .map(|e| e.to_string())
        .collect()
}

fn summarize(left_paths: &[LeftPath]) -> Summary {
    let mut summary = Summary {
        left_paths: left_paths.len(),
        ..Summary::default()
    };
    for lp in left_paths {
        if !lp.reachable {
            summary.left_pruned += 1;
        }
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
    }

    let s = &run.summary;
    let _ = writeln!(
        out,
        "\nsummary: {} left paths{}, {} right paths; {} GOAL FAILS, {} verified, {} unreachable, {} inconclusive{}",
        s.left_paths,
        if s.left_pruned > 0 {
            format!(" ({} pruned)", s.left_pruned)
        } else {
            String::new()
        },
        s.right_paths,
        s.goal_fails,
        s.verified,
        s.unreachable,
        s.inconclusive,
        if run.partial {
            "\n(PARTIAL: exploration stopped early — results are incomplete)"
        } else {
            ""
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
    use crate::project::{DirectoryFiles, DirectoryProject};
    use crate::util::smtsolver::cvc5lib::Cvc5LibBackend;

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
        with_project(dir, |proj| {
            // `into_path` keeps the dir around after the test so artifacts can be
            // inspected on failure (and so `run.out_dir` stays valid).
            let out = tempfile::tempdir().unwrap().into_path();
            let backend = Cvc5LibBackend::new(true, opts.timeout_ms);
            run_debug_command(
                proj, theorem, 0, oracle, claim, &opts, &backend, Some(out),
            )
            .unwrap()
        })
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
        // transcript replays as a coherent incremental session.
        let transcript =
            std::fs::read_to_string(std::path::Path::new(&run.out_dir).join("transcript.smt2"))
                .unwrap();
        assert!(transcript.contains("(check-sat)"));
        assert!(transcript.contains("(push 1)") && transcript.contains("(pop 1)"));
    }

    /// The epic's primary target, happy path: every pair Verified or
    /// Unreachable, exits ok, and the `Unreachable` verdict is actually
    /// exercised (a run that is all-green only because every pair is vacuous is
    /// the bug this distinction exists to catch).
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
        assert!(
            run.summary.unreachable > 0,
            "expected some pairs to be Unreachable, not just Verified"
        );
    }

    /// `--timeout 1` on a non-trivial claim: the goal checks that need real
    /// solving time out to `Inconclusive` rather than being reported `Verified`,
    /// and no pair regresses to a false `GOAL FAILS`.
    #[test]
    fn tiny_timeout_yields_inconclusive_never_a_false_pass() {
        let mut opts = DebugOptions::default();
        opts.timeout_ms = Some(1);
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
    }

    /// `--no-check-right` skips the vacuity check: it explores at least as many
    /// pairs and never introduces a `GOAL FAILS` the default run did not have.
    #[test]
    fn no_check_right_keeps_the_same_goal_fails_set() {
        let base = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            DebugOptions::default(),
        );
        let mut opts = DebugOptions::default();
        opts.check_right = false;
        let no_right = run_in_tmp(
            "example-projects/kem-dem/kem-dem-cca-ssp",
            "kem_dem_cca_ssp",
            "PKGEN",
            "same-output",
            opts,
        );
        assert_eq!(base.summary.goal_fails, no_right.summary.goal_fails);
        assert_eq!(no_right.summary.goal_fails, 0);
        assert!(no_right.summary.right_paths >= base.summary.right_paths);
        // vacuity is off, so pairs the default run called Unreachable now fall
        // through to Verified.
        assert!(no_right.summary.unreachable <= base.summary.unreachable);
    }

    #[test]
    fn max_paths_stops_early_and_flags_partial() {
        let mut opts = DebugOptions::default();
        opts.max_paths = 1;
        let run = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            opts,
        );
        assert!(run.partial);
        assert!(!run.is_ok());
    }

    #[test]
    fn check_left_prunes_abort_paths_without_changing_verdicts() {
        let base = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            DebugOptions::default(),
        );
        let mut opts = DebugOptions::default();
        opts.check_left = true;
        let pruned = run_in_tmp(
            "example-projects/simple-KEM-example",
            "KEM_Proof",
            "TestSender",
            "same-output",
            opts,
        );
        assert!(
            pruned.summary.left_pruned > 0,
            "expected some left abort paths to be pruned under `no-abort`"
        );
        // no GOAL FAILS in either mode
        assert_eq!(base.summary.goal_fails, 0);
        assert_eq!(pruned.summary.goal_fails, 0);
    }
}
