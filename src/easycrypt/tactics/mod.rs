// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt --tactics`: proofs from lockstep execution (story 27).
//!
//! For each selected oracle of each equivalence: run lockstep execution on the oracle
//! (`domino debug --easycrypt`'s engine, its artifacts written the same way), then walk the
//! joint tree alongside a live EasyCrypt session ([`driver`]), send each step, read the goals
//! back as JSON, and write down what EasyCrypt accepted as the oracle's bullet in `Eq_*.ec`.
//! What could not be closed is an `admit` labelled with the claim, the invariant relation, the
//! `J`/`S` id and what Domino itself concluded.
//!
//! - [`script`]: the accepted sentences, bullets and indentation.
//! - [`goals`]: reading goals from the JSON.
//! - [`driver`]: the prover.
//!
//! Plain `domino easycrypt` never gets here.

mod driver;
mod goals;
mod script;

use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use thiserror::Error;

use crate::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions};
use crate::debug::progress::NopObserver;
use crate::debug::smtout::SmtOut;
use crate::project::Project;
use crate::theorem::Theorem;
use crate::transforms::theorem_transforms::EasyCryptTransform;
use crate::transforms::TheoremTransform;
use crate::util::smtsolver::SmtSolverBackend;
use crate::writers::easycrypt::export::{EquivalenceReport, ExportedTheorem};
use crate::writers::easycrypt::lower::inline_oracle_ec;

use super::check::{
    describe_mismatch, equivalence_setup, ok_or_reject, sentences_until_call, CheckError,
    EquivalenceSetup,
};
use super::json::Goal;
use super::session::{split_sentences, Session, SessionError};

pub use driver::{Admit, AdmitReason, DominoView, OracleStats, Timeouts};
use driver::{OracleTree, Prover};

#[derive(Debug, Error)]
pub enum TacticsError {
    #[error(transparent)]
    Session(#[from] SessionError),
    #[error(transparent)]
    Check(#[from] CheckError),
    #[error(transparent)]
    Export(#[from] crate::writers::easycrypt::EcExportError),
    #[error(transparent)]
    Transform(#[from] crate::transforms::theorem_transforms::EquivalenceTransformError),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("invalid `ssp.toml`: {0}")]
    Config(String),
}

#[derive(Debug, Clone)]
pub struct TacticsOptions {
    /// Only this proofstep (index into the theorem's game hops).
    pub proofstep: Option<usize>,
    /// Only this exported oracle: the rest keep `+ proc; inline. admit.`.
    pub oracle: Option<String>,
    /// How long one EasyCrypt sentence may run (`--ec-timeout`).
    pub ec_timeout: Duration,
    /// Lemma names for the last `smt(…)` rungs: `ssp.toml` `[easycrypt] smt_hints`.
    pub smt_hints: Vec<String>,
    /// Per-query timeout of the lockstep engine's solver, in milliseconds.
    pub lockstep_timeout_ms: Option<u64>,
    /// Rung 0, `auto => /#.` on every program goal (§3.3). Off only to exercise the walk.
    pub rung0: bool,
    /// The most time splitting one leaf by meaning may take before its remaining parts are
    /// admitted.
    pub leaf_budget: Duration,
}

impl Default for TacticsOptions {
    fn default() -> Self {
        TacticsOptions {
            proofstep: None,
            oracle: None,
            ec_timeout: Duration::from_secs(60),
            smt_hints: Vec::new(),
            lockstep_timeout_ms: None,
            rung0: true,
            leaf_budget: Duration::from_secs(300),
        }
    }
}

/// Rung 0's timeout, at most (`auto => /#.` on every program goal).
const RUNG0_TIMEOUT: Duration = Duration::from_secs(2);

/// The lemma names of `ssp.toml`'s `[easycrypt] smt_hints = [...]` (optional).
pub fn read_smt_hints(project_root: &Path) -> Result<Vec<String>, TacticsError> {
    let path = project_root.join("ssp.toml");
    let Ok(text) = std::fs::read_to_string(&path) else {
        return Ok(Vec::new());
    };
    parse_smt_hints(&text)
}

pub(crate) fn parse_smt_hints(text: &str) -> Result<Vec<String>, TacticsError> {
    let value: toml::Value = text
        .parse()
        .map_err(|e: toml::de::Error| TacticsError::Config(e.to_string()))?;
    let Some(hints) = value.get("easycrypt").and_then(|t| t.get("smt_hints")) else {
        return Ok(Vec::new());
    };
    let items = hints.as_array().ok_or_else(|| {
        TacticsError::Config("`[easycrypt] smt_hints` must be a list of lemma names".into())
    })?;
    items
        .iter()
        .map(|item| {
            let name = item.as_str().ok_or_else(|| {
                TacticsError::Config("`[easycrypt] smt_hints` holds non-strings".into())
            })?;
            let valid = !name.is_empty()
                && name
                    .chars()
                    .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.' | '\''));
            if !valid {
                return Err(TacticsError::Config(format!(
                    "`{name}` in `[easycrypt] smt_hints` is not a lemma name"
                )));
            }
            Ok(name.to_string())
        })
        .collect()
}

/// What happened to one oracle.
#[derive(Debug, Clone)]
pub struct OracleTactics {
    pub oracle: String,
    /// Set when no tactics could be produced (lockstep failed, no goal): the bullet stays
    /// `admit`.
    pub problem: Option<String>,
    pub stats: OracleStats,
    /// Alignment mismatches (their descriptions): the oracle used the fallback.
    pub alignment_mismatches: Vec<String>,
    pub joint_paths: usize,
    pub nodes: usize,
    pub stuck_points: usize,
    pub lockstep_time: Duration,
    pub easycrypt_time: Duration,
    /// The bullet as written into the file.
    pub script: String,
    /// `easycrypt compile` rejected this oracle's script though the session accepted every
    /// sentence: the oracle was written as `admit` only. A bug to report.
    pub reverted: bool,
}

impl OracleTactics {
    fn empty(oracle: &str, problem: &str) -> OracleTactics {
        OracleTactics {
            oracle: oracle.to_string(),
            problem: Some(problem.to_string()),
            stats: OracleStats::default(),
            alignment_mismatches: vec![],
            joint_paths: 0,
            nodes: 0,
            stuck_points: 0,
            lockstep_time: Duration::ZERO,
            easycrypt_time: Duration::ZERO,
            script: String::new(),
            reverted: false,
        }
    }

    /// Admits by reason, in the order of [`AdmitReason::ALL`], nonzero only.
    pub fn admits_by_reason(&self) -> Vec<(AdmitReason, usize)> {
        AdmitReason::ALL
            .iter()
            .map(|&r| {
                (
                    r,
                    self.stats.admits.iter().filter(|a| a.reason == r).count(),
                )
            })
            .filter(|&(_, n)| n > 0)
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct EquivalenceTactics {
    pub proofstep: usize,
    pub proof_file: String,
    pub left: String,
    pub right: String,
    pub oracles: Vec<OracleTactics>,
    /// The base case did not close and was admitted.
    pub base_case_admitted: bool,
    pub elapsed: Duration,
    /// The written report, `Eq_<L>_<R>.report.txt` in the theorem's output directory.
    pub report_file: String,
}

#[derive(Debug, Clone)]
pub struct TheoremTactics {
    pub theorem: String,
    pub equivalences: Vec<EquivalenceTactics>,
    pub elapsed: Duration,
    pub transcript: PathBuf,
}

impl TheoremTactics {
    /// Every oracle of the theorem, in the order of the report.
    pub fn oracles(&self) -> impl Iterator<Item = &OracleTactics> {
        self.equivalences.iter().flat_map(|e| e.oracles.iter())
    }

    /// The `admit` count over all translated oracles.
    pub fn admit_count(&self) -> usize {
        self.oracles().map(|o| o.stats.admits.len()).sum()
    }
}

/// The whole of `--tactics` for one exported theorem, already written to `out_dir`: rewrites
/// the selected `Eq_*.ec` files, writes their reports and the transcript, and returns what it
/// did.
pub fn run_tactics<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
) -> Result<TheoremTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();
    let (theorem_ec, _aux) = EasyCryptTransform.transform_theorem(theorem)?;
    let out_dir = std::fs::canonicalize(out_dir).unwrap_or_else(|_| out_dir.to_path_buf());
    let progress_dir = out_dir.join("progress");
    std::fs::create_dir_all(&progress_dir)?;
    let transcript_path = progress_dir.join("ec-transcript.jsonl");
    let transcript = File::create(&transcript_path)?;

    let mut equivalences = Vec::new();
    for eq in &exported.equivalences {
        if options.proofstep.is_some_and(|p| p != eq.proofstep) {
            continue;
        }
        equivalences.push(tactics_for_equivalence(
            theorem,
            &theorem_ec,
            project,
            exported,
            eq,
            &out_dir,
            backend,
            options,
            transcript.try_clone()?,
        )?);
    }
    Ok(TheoremTactics {
        theorem: theorem.name.clone(),
        equivalences,
        elapsed: started.elapsed(),
        transcript: transcript_path,
    })
}

#[allow(clippy::too_many_arguments)]
fn tactics_for_equivalence<P, B>(
    theorem: &Theorem<'_>,
    theorem_ec: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    eq: &EquivalenceReport,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
    transcript: File,
) -> Result<EquivalenceTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();
    let file = eq.proof_file.clone();
    let source = exported
        .files
        .get(Path::new(&file))
        .ok_or_else(|| CheckError::MissingFile { file: file.clone() })?;
    let setup = equivalence_setup(theorem_ec, eq)?;
    let selected = |name: &str| options.oracle.as_deref().is_none_or(|w| w == name);
    if let Some(wanted) = &options.oracle {
        if !setup.oracles.iter().any(|(name, _)| name == wanted) {
            return Err(CheckError::NoSuchOracle {
                oracle: wanted.clone(),
                file,
            }
            .into());
        }
    }

    // open the proof: everything up to `call (…); last first.`, then the base case
    let sentences = split_sentences(source);
    let call_prefix = sentences_until_call(&file, source)?;
    let mut session = Session::start(out_dir)?;
    session.set_transcript_sink(Box::new(transcript), &file);
    session.set_timeout(options.ec_timeout);
    for sentence in &call_prefix {
        ok_or_reject(session.send(sentence)?, &file, sentence)?;
    }
    let mut base_case_admitted = false;
    if let Some(base) = sentences.get(call_prefix.len()) {
        if session.send(base)?.status != super::json::Status::Ok {
            base_case_admitted = true;
            session.send("admit.")?;
        }
    }

    let mut results: Vec<OracleTactics> = Vec::new();
    while let Some(goal) = session.goals().first() {
        let target = setup.oracle_of_goal(goal).filter(|o| selected(o));
        match target {
            Some(oracle) => {
                let result = tactics_for_oracle(
                    &mut session,
                    project,
                    theorem,
                    eq,
                    &setup,
                    &oracle,
                    backend,
                    options,
                )?;
                results.push(result);
            }
            None => {
                // the base case (admitted above), or an oracle that was not asked for
                session.send("admit.")?;
            }
        }
    }
    let position = |name: &str| setup.oracles.iter().position(|(n, _)| n == name);
    for (name, _) in &setup.oracles {
        if selected(name) && !results.iter().any(|r| &r.oracle == name) {
            results.push(OracleTactics::empty(
                name,
                "no goal for this oracle after `call (…); last first.`",
            ));
        }
    }
    results.sort_by_key(|r| position(&r.oracle));
    drop(session);

    // write the file and check it with `easycrypt compile` (§3.7)
    let text_of = |scripts: &[&OracleTactics]| {
        let mut text = source.clone();
        for o in scripts {
            let proc_name = &setup
                .oracles
                .iter()
                .find(|(n, _)| *n == o.oracle)
                .expect("a result names an exported oracle")
                .1;
            let marker = format!("(* {proc_name} *)\n+ proc; inline. admit.");
            let replacement = format!("(* {proc_name} *)\n{}", o.script.trim_end());
            text = text.replacen(&marker, &replacement, 1);
        }
        text
    };
    let scripted: Vec<usize> = (0..results.len())
        .filter(|&i| !results[i].script.is_empty())
        .collect();
    let binary = super::session::locate_binary();
    let file_path = out_dir.join(&file);
    if !scripted.is_empty() {
        let all: Vec<&OracleTactics> = scripted.iter().map(|&i| &results[i]).collect();
        std::fs::write(&file_path, text_of(&all))?;
        if compile(&binary, out_dir, &file).is_err() {
            // the session accepted every sentence and the compiler does not: find which
            // oracles are at fault, and write those as `admit` only
            let mut keep = Vec::new();
            for &i in &scripted {
                std::fs::write(&file_path, text_of(&[&results[i]]))?;
                if compile(&binary, out_dir, &file).is_ok() {
                    keep.push(i);
                } else {
                    results[i].reverted = true;
                }
            }
            let kept: Vec<&OracleTactics> = keep.iter().map(|&i| &results[i]).collect();
            std::fs::write(&file_path, text_of(&kept))?;
        }
    }

    let report_file = file.trim_end_matches(".ec").to_string() + ".report.txt";
    let tactics = EquivalenceTactics {
        proofstep: eq.proofstep,
        proof_file: file,
        left: eq.left_name.clone(),
        right: eq.right_name.clone(),
        oracles: results,
        base_case_admitted,
        elapsed: started.elapsed(),
        report_file,
    };
    std::fs::write(out_dir.join(&tactics.report_file), tactics.render())?;
    Ok(tactics)
}

#[allow(clippy::too_many_arguments)]
fn tactics_for_oracle<P, B>(
    session: &mut Session,
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    setup: &EquivalenceSetup<'_>,
    oracle: &str,
    backend: &B,
    options: &TacticsOptions,
) -> Result<OracleTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    eprintln!("tactics: oracle {oracle} of {}", eq.proof_file);
    // lockstep execution first: its artifacts are written exactly as `domino debug --easycrypt`
    // writes them, so every `S`/`J` of an admit has a page to open
    let lockstep_started = Instant::now();
    let run = run_lockstep_command(
        project,
        &theorem.name,
        eq.proofstep,
        oracle,
        &LockstepDebugOptions {
            timeout_ms: options.lockstep_timeout_ms,
            max_paths: None,
            smt_out: SmtOut::Failures,
            transcript: false,
        },
        backend,
        None,
        &mut NopObserver,
        None,
    );
    let lockstep_time = lockstep_started.elapsed();
    let run = match run {
        Ok(run) => run,
        Err(source) => {
            session.send("admit.")?;
            let mut result =
                OracleTactics::empty(oracle, &format!("lockstep execution failed: {source}"));
            result.lockstep_time = lockstep_time;
            return Ok(result);
        }
    };

    let tree = OracleTree::new(&run.outcome);
    // the operators `inv` unfolds to, by name (`writers::easycrypt::invariant`)
    let unfold_ops: Vec<String> = ["inv".to_string(), "params_inv".to_string()]
        .into_iter()
        .chain(
            run.meta
                .goals
                .relations
                .iter()
                .map(|r| format!("Domino_{}", r.name)),
        )
        .collect();
    let left_ir = inline_oracle_ec(setup.left_inst, oracle)?;
    let right_ir = inline_oracle_ec(setup.right_inst, oracle)?;
    let mut prover = Prover {
        session,
        script: Default::default(),
        tree: &tree,
        hints: &options.smt_hints,
        unfold_ops: &unfold_ops,
        rung0: options.rung0,
        oracle,
        leaf_budget: options.leaf_budget,
        deadline: None,
        timeouts: Timeouts {
            general: options.ec_timeout,
            rung0: RUNG0_TIMEOUT.min(options.ec_timeout),
        },
        stats: OracleStats::default(),
    };
    let began = Instant::now();
    let mismatches = prover.oracle(|goal: &Goal| {
        match super::check::align_goal(
            goal,
            (&left_ir, &setup.left_flag),
            (&right_ir, &setup.right_flag),
        ) {
            None => vec!["`proc; inline.` did not give an equivS goal".to_string()],
            Some(sides) => sides
                .iter()
                .flat_map(|s| s.alignment.mismatches.iter().map(describe_mismatch))
                .collect(),
        }
    })?;
    let easycrypt_time = began.elapsed();
    let script = prover.script.render();
    let stats = prover.stats;
    Ok(OracleTactics {
        oracle: oracle.to_string(),
        problem: None,
        stats,
        alignment_mismatches: mismatches,
        joint_paths: run.summary.joint_paths,
        nodes: run.summary.nodes,
        stuck_points: run.summary.stuck_points,
        lockstep_time,
        easycrypt_time,
        script,
        reverted: false,
    })
}

/// The most `easycrypt compile` of one written file may take.
const COMPILE_TIMEOUT: Duration = Duration::from_secs(30 * 60);

/// `easycrypt compile -I <dir> <file>`; `Err` carries the tail of its output.
fn compile(binary: &Path, dir: &Path, file: &str) -> Result<(), String> {
    let stderr = tempfile::tempfile().map_err(|e| e.to_string())?;
    let mut child = Command::new(binary)
        .args(["compile", "-I"])
        .arg(dir)
        .arg(file)
        .current_dir(dir)
        .stdout(std::process::Stdio::null())
        .stderr(stderr.try_clone().map_err(|e| e.to_string())?)
        .spawn()
        .map_err(|e| e.to_string())?;
    let began = Instant::now();
    let status = loop {
        match child.try_wait().map_err(|e| e.to_string())? {
            Some(status) => break status,
            None if began.elapsed() > COMPILE_TIMEOUT => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("timed out after {}s", COMPILE_TIMEOUT.as_secs()));
            }
            None => std::thread::sleep(Duration::from_millis(200)),
        }
    };
    if status.success() {
        return Ok(());
    }
    use std::io::{Read, Seek};
    let mut text = String::new();
    let mut stderr = stderr;
    let _ = stderr.rewind();
    let _ = stderr.read_to_string(&mut text);
    let tail: Vec<&str> = text.lines().rev().take(8).collect();
    Err(tail.into_iter().rev().collect::<Vec<_>>().join("\n"))
}

fn secs(d: Duration) -> String {
    format!("{:.1}s", d.as_secs_f32())
}

impl EquivalenceTactics {
    /// The report: `Eq_<L>_<R>.report.txt`, and the same text on stdout.
    pub fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "tactics for {} (proofstep {}: {} ~ {})",
            self.proof_file, self.proofstep, self.left, self.right
        );
        if self.base_case_admitted {
            let _ = writeln!(out, "  the base case did not close and was admitted");
        }
        for o in &self.oracles {
            if let Some(problem) = &o.problem {
                let _ = writeln!(out, "  {}: no tactics ({problem})", o.oracle);
                continue;
            }
            let _ = writeln!(
                out,
                "  {}: lockstep {} joint paths, {} nodes, {} stuck points ({})",
                o.oracle,
                o.joint_paths,
                o.nodes,
                o.stuck_points,
                secs(o.lockstep_time)
            );
            let by_reason = o.admits_by_reason();
            let admits = if by_reason.is_empty() {
                "no admit".to_string()
            } else {
                let parts: Vec<String> = by_reason
                    .iter()
                    .map(|(r, n)| format!("{} {n}", r.slug()))
                    .collect();
                format!("{} admits ({})", o.stats.admits.len(), parts.join(", "))
            };
            let _ = writeln!(
                out,
                "    goals closed: {}, {admits}, fallbacks: {}, EasyCrypt time {} ({} attempts undone)",
                o.stats.closed,
                o.stats.fallbacks,
                secs(o.easycrypt_time),
                o.stats.attempts_undone
            );
            if o.reverted {
                let _ = writeln!(
                    out,
                    "    BUG: `easycrypt compile` rejected this script though the session accepted \
                     every sentence; the oracle was written as `admit` only"
                );
            }
            for m in &o.alignment_mismatches {
                let _ = writeln!(out, "    alignment mismatch (fallback used): {m}");
            }
            for a in &o.stats.admits {
                let _ = writeln!(
                    out,
                    "    admit {} {} [{}] Domino: {}",
                    a.id,
                    a.claim,
                    a.reason.slug(),
                    a.domino.slug()
                );
                if a.reason == AdmitReason::DominoVerifiedEcFailed {
                    let goal: String = a.goal.chars().take(4000).collect();
                    let _ = writeln!(out, "      goal: {goal}");
                }
            }
        }
        let closed: usize = self.oracles.iter().map(|o| o.stats.closed).sum();
        let admits: usize = self.oracles.iter().map(|o| o.stats.admits.len()).sum();
        let _ = writeln!(
            out,
            "{} oracles, {closed} goals closed, {admits} admits, {}",
            self.oracles.len(),
            secs(self.elapsed)
        );
        out
    }
}

impl TheoremTactics {
    pub fn render(&self) -> String {
        let mut out = format!("tactics for theorem {}\n", self.theorem);
        for eq in &self.equivalences {
            out.push_str(&eq.render());
        }
        let _ = writeln!(
            out,
            "transcript: {} ({})",
            self.transcript.display(),
            secs(self.elapsed)
        );
        out
    }
}

#[cfg(test)]
mod tests;
