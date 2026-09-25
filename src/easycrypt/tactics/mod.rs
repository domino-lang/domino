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
//! **The file on disk is what has been proved so far** (story 33): `Eq_*.ec` and its report are
//! rewritten together, atomically, after every oracle (or, with [`WriteGranularity::Node`],
//! after every joint node, the oracle in flight **sealed**). Nothing compiles the written file
//! during a run (ADR 0005): every sentence in it was accepted by the live session.
//!
//! **Ctrl-C** (story 34, [`TacticsOptions::stop`]) stops the run where it stands: the running
//! EasyCrypt sentence is interrupted, lockstep execution stops at its next node, the oracle in
//! flight is sealed and written, and the result says so ([`Interrupted`]).
//!
//! - [`script`]: the accepted sentences, bullets and indentation.
//! - [`goals`]: reading goals from the JSON.
//! - [`driver`]: the prover.
//! - [`live`], `live::page`: the live translation page, `progress/index.html` (story 28).
//!
//! Plain `domino easycrypt` never gets here.

mod driver;
mod goals;
mod live;
mod script;

use std::fmt::Write as _;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use thiserror::Error;

use crate::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions};
use crate::debug::progress::NopObserver;
use crate::writers::easycrypt::progress::{ExportObserver, NopExportObserver};
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

pub use super::transcript::{EcTranscriptMode, GOALS_PER_STEP, GOAL_TEXT_CAP};
pub use live::{strip_timings, LiveConfig, LiveHandle};

pub use driver::{Admit, AdmitReason, DominoView, OracleStats, Timeouts};
use driver::{OracleTree, Prover, Sealed};

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
    /// What `ec-transcript.jsonl` keeps of EasyCrypt's answers (`--ec-transcript`).
    pub ec_transcript: EcTranscriptMode,
    /// How often `Eq_*.ec` and its report are written (`--write-granularity`).
    pub write_granularity: WriteGranularity,
    /// Set by a Ctrl-C handler to stop the run (story 34). The run then stops where it stands,
    /// seals the oracle in flight and returns normally, its result [`Interrupted`].
    pub stop: Option<Arc<AtomicBool>>,
}

impl TacticsOptions {
    fn stop_requested(&self) -> bool {
        self.stop.as_ref().is_some_and(|s| s.load(Ordering::Relaxed))
    }
}

/// Where a Ctrl-C stopped a tactics run (story 34). Oracles finished before keep their scripts,
/// oracles not reached keep `+ proc; inline. admit.`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Interrupted {
    /// While the proof was being opened, or between two oracles.
    NoOracleInFlight,
    /// During the oracle's lockstep execution, before it sent anything: it keeps its
    /// `+ proc; inline. admit.`.
    Lockstep { oracle: String },
    /// While the oracle was being proved: it was sealed with `admits` admits labelled
    /// `interrupted`, at `node` (`N<k>`, or `router`).
    Sealed {
        oracle: String,
        admits: usize,
        node: String,
    },
}

impl std::fmt::Display for Interrupted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Interrupted::NoOracleInFlight => write!(f, "no oracle was in flight"),
            Interrupted::Lockstep { oracle } => {
                write!(f, "during lockstep execution of {oracle}, nothing sealed")
            }
            Interrupted::Sealed {
                oracle,
                admits,
                node,
            } => write!(f, "sealed {oracle} with {admits} admits at node {node}"),
        }
    }
}

/// When a tactics run writes `Eq_*.ec` and its report (story 33). Both are one mechanism: seal
/// the oracle in flight, write, continue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteGranularity {
    /// After each oracle (the default): nothing is open then, so the seal changes nothing.
    Oracle,
    /// After every joint node too, the oracle in flight sealed: to watch a long oracle's proof
    /// accumulate.
    Node,
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
            ec_transcript: EcTranscriptMode::Capped,
            write_granularity: WriteGranularity::Oracle,
            stop: None,
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
    /// The run was stopped by Ctrl-C while on this equivalence (story 34).
    pub interrupted: Option<Interrupted>,
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

    /// Where Ctrl-C stopped the run, if it did (story 34): the run ended there.
    pub fn interrupted(&self) -> Option<&Interrupted> {
        self.equivalences
            .iter()
            .find_map(|e| e.interrupted.as_ref())
    }
}

/// The whole of `--tactics` for one exported theorem, already written to `out_dir`: rewrites
/// the selected `Eq_*.ec` files, writes their reports, the transcript and the live page
/// (`progress/index.html`), and returns what it did.
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
    run_tactics_observed(
        theorem,
        project,
        exported,
        out_dir,
        backend,
        options,
        Box::new(NopExportObserver),
        &[],
    )
}

/// [`run_tactics`], reporting the `tactics` phase to `progress` (per oracle and per goal) and
/// listing `phases`, the export phases that ran before (name, item count), on the page.
#[allow(clippy::too_many_arguments)]
pub fn run_tactics_observed<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
    progress: Box<dyn ExportObserver>,
    phases: &[(&'static str, usize)],
) -> Result<TheoremTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let out_dir = std::fs::canonicalize(out_dir).unwrap_or_else(|_| out_dir.to_path_buf());
    let progress_dir = out_dir.join("progress");
    std::fs::create_dir_all(&progress_dir)?;
    let live = LiveHandle::new(LiveConfig {
        theorem: theorem.name.clone(),
        page: Some(progress_dir.join("index.html")),
        transcript: progress_dir.join("ec-transcript.jsonl"),
        phases: phases.to_vec(),
        progress,
    });
    let result = run_tactics_inner(
        theorem, project, exported, &out_dir, backend, options, &live,
    );
    // the last write always happens: the page on disk matches the end state
    match &result {
        Ok(tactics) => match tactics.interrupted() {
            Some(at) => live.interrupted(&at.to_string()),
            None => live.finish(),
        },
        Err(e) => live.fail(&e.to_string()),
    }
    result
}

fn run_tactics_inner<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
    live: &LiveHandle,
) -> Result<TheoremTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let started = Instant::now();
    let (theorem_ec, _aux) = EasyCryptTransform.transform_theorem(theorem)?;
    let progress_dir = out_dir.join("progress");
    let transcript_path = progress_dir.join("ec-transcript.jsonl");
    // one file for every equivalence; `None` once a capped write failed (story 31 §3.3)
    let mut transcript = Some(File::create(&transcript_path)?);

    let mut equivalences = Vec::new();
    for eq in &exported.equivalences {
        if options.proofstep.is_some_and(|p| p != eq.proofstep) {
            continue;
        }
        let tactics = tactics_for_equivalence(
            theorem,
            &theorem_ec,
            project,
            exported,
            eq,
            out_dir,
            backend,
            options,
            &mut transcript,
            &transcript_path,
            live,
        )?;
        let interrupted = tactics.interrupted.is_some();
        equivalences.push(tactics);
        if interrupted {
            break;
        }
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
    transcript: &mut Option<File>,
    transcript_path: &Path,
    live: &LiveHandle,
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
    let selected_oracles: Vec<String> = setup
        .oracles
        .iter()
        .map(|(name, _)| name.clone())
        .filter(|name| selected(name))
        .collect();
    live.equivalence_started(&file, eq.proofstep, &eq.left_name, &eq.right_name, &selected_oracles);
    let report_file = file.trim_end_matches(".ec").to_string() + ".report.txt";
    let mut proof = ProofFile {
        source,
        procs: &setup.oracles,
        out_dir,
        started,
        tactics: EquivalenceTactics {
            proofstep: eq.proofstep,
            proof_file: file.clone(),
            left: eq.left_name.clone(),
            right: eq.right_name.clone(),
            oracles: Vec::new(),
            base_case_admitted: false,
            elapsed: Duration::ZERO,
            report_file,
            interrupted: None,
        },
    };
    // Ctrl-C (story 34): the equivalence ends where it stands, with what is written
    let interrupted = 'run: {
        if options.stop_requested() {
            break 'run Some(Interrupted::NoOracleInFlight);
        }
        live.activity("starting EasyCrypt and opening the proof");
        let mut session = Session::start(out_dir)?;
        if let Some(transcript) = transcript {
            session.set_transcript_sink(
                Box::new(transcript.try_clone()?),
                transcript_path,
                options.ec_transcript,
                &file,
            );
        }
        session.set_observer(live.session_observer());
        session.set_timeout(options.ec_timeout);
        if let Some(stop) = &options.stop {
            session.set_stop(stop.clone());
        }
        for sentence in &call_prefix {
            let response = session.send(sentence)?;
            if options.stop_requested() {
                break 'run Some(Interrupted::NoOracleInFlight);
            }
            ok_or_reject(response, &file, sentence)?;
        }
        if let Some(base) = sentences.get(call_prefix.len()) {
            if session.send(base)?.status != super::json::Status::Ok {
                if options.stop_requested() {
                    break 'run Some(Interrupted::NoOracleInFlight);
                }
                proof.tactics.base_case_admitted = true;
                session.send("admit.")?;
            }
        }

        let mut interrupted = None;
        while let Some(goal) = session.goals().first() {
            if options.stop_requested() {
                interrupted = Some(Interrupted::NoOracleInFlight);
                break;
            }
            let target = setup.oracle_of_goal(goal).filter(|o| selected(o));
            match target {
                Some(oracle) => {
                    let end = tactics_for_oracle(
                        &mut session,
                        project,
                        theorem,
                        eq,
                        &setup,
                        &oracle,
                        backend,
                        options,
                        live,
                        &mut proof,
                    )?;
                    let (result, stopped) = match end {
                        OracleEnd::Done(result) => (Some(result), None),
                        OracleEnd::Stopped { sealed, at } => (sealed, Some(at)),
                    };
                    if let Some(result) = result {
                        proof.tactics.oracles.push(result);
                        proof.write(None)?;
                        live.oracle_finished(proof.tactics.oracles.last().expect("just pushed"));
                    }
                    if stopped.is_some() {
                        interrupted = stopped;
                        break;
                    }
                }
                None => {
                    // the base case (admitted above), or an oracle that was not asked for
                    session.send("admit.")?;
                }
            }
        }
        if interrupted.is_none() {
            for (name, _) in &setup.oracles {
                if selected(name) && !proof.tactics.oracles.iter().any(|r| &r.oracle == name) {
                    let empty = OracleTactics::empty(
                        name,
                        "no goal for this oracle after `call (…); last first.`",
                    );
                    live.oracle_finished(&empty);
                    proof.tactics.oracles.push(empty);
                }
            }
        }
        if session.transcript_dropped() {
            // a later record would start at an offset the live page does not know
            *transcript = None;
        }
        interrupted
    };
    proof.tactics.interrupted = interrupted;

    let tactics = proof.write(None)?;
    live.equivalence_finished(&tactics);
    Ok(tactics)
}

/// Where lockstep execution of `oracle` writes its artifacts: beside the export it describes,
/// under the theorem it belongs to (story 19 §4.6). `domino easycrypt --debug` writes there too.
pub fn debug_dir(theorem_out: &Path, left: &str, right: &str, oracle: &str) -> PathBuf {
    theorem_out
        .join("!debug!")
        .join(format!("{left}-{right}"))
        .join(oracle)
}

/// `Eq_*.ec` and its report as a tactics run goes (story 33): both are rewritten on every
/// write, each atomically, so the file on disk is what has been proved so far and the report
/// next to it describes that file. No `easycrypt compile` (ADR 0005).
struct ProofFile<'a> {
    /// The exported file: every oracle `+ proc; inline. admit.`.
    source: &'a str,
    /// `(exported name, EasyCrypt's procedure name)` of every oracle, in the file's order.
    procs: &'a [(String, String)],
    /// The theorem's output directory: the file, the report, and `progress/` for the
    /// temporary files.
    out_dir: &'a Path,
    /// When the equivalence started: the report's elapsed time.
    started: Instant,
    /// The equivalence so far: its finished oracles, in the order they finished.
    tactics: EquivalenceTactics,
}

impl ProofFile<'_> {
    /// Writes the file and its report: the finished oracles and `in_flight`, an oracle sealed
    /// part way through. Oracles not reached keep `+ proc; inline. admit.`. Returns what was
    /// written, the oracles in the file's order.
    fn write(&self, in_flight: Option<&OracleTactics>) -> std::io::Result<EquivalenceTactics> {
        let mut now = self.tactics.clone();
        now.oracles.extend(in_flight.cloned());
        now.oracles
            .sort_by_key(|o| self.procs.iter().position(|(n, _)| *n == o.oracle));
        now.elapsed = self.started.elapsed();
        // the report first: a reader who sees the file finds a report at least as new
        let tmp_dir = self.out_dir.join("progress");
        write_atomically(
            &self.out_dir.join(&now.report_file),
            &tmp_dir,
            &now.render(),
        )?;
        write_atomically(
            &self.out_dir.join(&now.proof_file),
            &tmp_dir,
            &self.text(&now.oracles),
        )?;
        Ok(now)
    }

    /// The exported file with each oracle's script in place of its `+ proc; inline. admit.`.
    fn text(&self, oracles: &[OracleTactics]) -> String {
        let mut text = self.source.to_string();
        for o in oracles.iter().filter(|o| !o.script.is_empty()) {
            let (_, proc_name) = self
                .procs
                .iter()
                .find(|(n, _)| *n == o.oracle)
                .expect("a result names an exported oracle");
            let marker = format!("(* {proc_name} *)\n+ proc; inline. admit.");
            let replacement = format!("(* {proc_name} *)\n{}", o.script.trim_end());
            text = text.replacen(&marker, &replacement, 1);
        }
        text
    }
}

/// Writes `text` to `path` through a temporary file in `tmp_dir` (on the same file system) and
/// a rename, so a reader, or a run killed part way, never leaves a half-written file. The
/// temporary file is synced before the rename, so a crash does not leave an empty file either.
/// It is in `progress/`, a run artifact (story 32), so a leftover one blocks nothing.
fn write_atomically(path: &Path, tmp_dir: &Path, text: &str) -> std::io::Result<()> {
    use std::io::Write as _;
    let name = path.file_name().expect("a file path").to_string_lossy();
    let tmp = tmp_dir.join(format!(".{name}.tmp"));
    let mut file = File::create(&tmp)?;
    file.write_all(text.as_bytes())?;
    file.sync_all()?;
    std::fs::rename(&tmp, path)
}

/// How [`tactics_for_oracle`] ended.
enum OracleEnd {
    /// The oracle's bullet is closed, or there was nothing to prove it with (`problem`).
    Done(OracleTactics),
    /// The run was asked to stop (Ctrl-C). `sealed` is the oracle as far as the walk got,
    /// `None` if lockstep execution was stopped before anything was sent.
    Stopped {
        sealed: Option<OracleTactics>,
        at: Interrupted,
    },
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
    live: &LiveHandle,
    proof: &mut ProofFile<'_>,
) -> Result<OracleEnd, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    live.oracle_started(oracle);
    // lockstep execution first: its artifacts are written exactly as `domino easycrypt --debug`
    // writes them, so every `S`/`J` of an admit has a page to open
    let lockstep_started = Instant::now();
    live.activity("lockstep execution");
    let run = run_lockstep_command(
        project,
        &theorem.name,
        eq.proofstep,
        oracle,
        &LockstepDebugOptions::easycrypt(options.lockstep_timeout_ms),
        backend,
        // next to the export it describes: `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/`
        Some(debug_dir(proof.out_dir, &eq.left_name, &eq.right_name, oracle)),
        &mut NopObserver,
        options.stop.as_deref(),
    );
    let lockstep_time = lockstep_started.elapsed();
    live.activity("");
    if options.stop_requested() {
        // lockstep execution was stopped, or has just finished: nothing was sent
        return Ok(OracleEnd::Stopped {
            sealed: None,
            at: Interrupted::Lockstep {
                oracle: oracle.to_string(),
            },
        });
    }
    if let Ok(run) = &run {
        live.lockstep_done(Path::new(&run.meta.out_dir));
    }
    let run = match run {
        Ok(run) => run,
        Err(source) => {
            session.send("admit.")?;
            let mut result =
                OracleTactics::empty(oracle, &format!("lockstep execution failed: {source}"));
            result.lockstep_time = lockstep_time;
            return Ok(OracleEnd::Done(result));
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
    let began = Instant::now();
    let result_of = |sealed: Sealed| OracleTactics {
        oracle: oracle.to_string(),
        problem: None,
        stats: sealed.stats,
        alignment_mismatches: sealed.mismatches,
        joint_paths: run.summary.joint_paths,
        nodes: run.summary.nodes,
        stuck_points: run.summary.stuck_points,
        lockstep_time,
        easycrypt_time: began.elapsed(),
        script: sealed.script,
    };
    // `--write-granularity node`: seal, write, continue. A failed write stops the writes; the
    // last good one stays on disk and the error ends the run after the oracle.
    let mut write_failed: Option<std::io::Error> = None;
    let mut write_sealed = |sealed: Sealed| {
        if write_failed.is_none() {
            let partial = result_of(sealed);
            if let Err(e) = proof.write(Some(&partial)) {
                write_failed = Some(e);
            }
        }
    };
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
        live: Some(live.clone()),
        checkpoint: match options.write_granularity {
            WriteGranularity::Oracle => None,
            WriteGranularity::Node => Some(&mut write_sealed),
        },
        node: None,
        mismatches: Vec::new(),
        stopped: None,
    };
    let proved = prover.oracle(|goal: &Goal| {
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
    });
    let stopped = match proved {
        Ok(()) => None,
        Err(SessionError::Stopped) => Some(
            prover
                .stopped
                .take()
                .expect("the walk seals the oracle before it stops"),
        ),
        Err(e) => return Err(e.into()),
    };
    let stopped_at = stopped.as_ref().map(|sealed| sealed.node.clone());
    // the oracle's bullet is closed and the seal is the script as it is, or the walk sealed it
    // where it stopped
    let sealed = stopped.unwrap_or_else(|| prover.seal());
    drop(prover);
    if let Some(e) = write_failed {
        return Err(e.into());
    }
    let result = result_of(sealed);
    let Some(node) = stopped_at else {
        return Ok(OracleEnd::Done(result));
    };
    let at = Interrupted::Sealed {
        oracle: oracle.to_string(),
        admits: result
            .stats
            .admits
            .iter()
            .filter(|a| a.reason == AdmitReason::Interrupted)
            .count(),
        node,
    };
    Ok(OracleEnd::Stopped {
        sealed: Some(result),
        at,
    })
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
        if let Some(at) = &self.interrupted {
            let _ = writeln!(out, "interrupted: {at}");
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
