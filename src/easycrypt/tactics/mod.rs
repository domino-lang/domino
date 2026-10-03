// SPDX-License-Identifier: MIT OR Apache-2.0

//! `domino easycrypt prove`: proofs from lockstep execution (story 27).
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
//! after every joint node, or, with [`WriteGranularity::Tactic`], the default, after every accepted
//! sentence, the oracle in flight **sealed**). Nothing compiles the written file
//! during a run (ADR 0005): every sentence in it was accepted by the live session.
//!
//! **Ctrl-C** (story 34, [`TacticsOptions::stop`]) stops the run where it stands: the running
//! EasyCrypt sentence is interrupted, lockstep execution stops at its next node, the oracle in
//! flight is sealed and written, and the result says so ([`Interrupted`]).
//!
//! **An unanswered interrupt** (`SessionError::Unresponsive`: EasyCrypt did not answer the
//! interrupts [`Session::send`] kept sending) seals the oracle in flight like a Ctrl-C, but the
//! job goes on: the stuck EasyCrypt is replaced by a fresh one opened at the same proof (a
//! **respawn**, [`respawn`]), the oracles already in the file are admitted there, and the walk
//! carries on with the next oracle. After [`MAX_RESPAWNS`] respawns the next one ends the job
//! ([`EquivalenceTactics::ended_early`]). An answer that shows EasyCrypt *swallowed* an interrupt
//! is warned about once per run ([`SwallowWatch`]).
//!
//! **Resuming an interrupted oracle** (ADR 0008, [`ResumeMode`]): lockstep execution's joint tree
//! is saved beside the session record (`Eq_<L>_<R>.<oracle>.tree.json`) before the oracle's first
//! sentence. An oracle the record holds as `interrupted` is walked again on that saved tree, its
//! closed nodes kept, instead of being proved from scratch.
//!
//! - [`script`]: the accepted sentences, bullets and indentation.
//! - [`goals`]: reading goals from the JSON.
//! - [`driver`]: the prover.
//! - [`live`], `live::page`: the live translation page, `progress/Eq_<L>_<R>/index.html` (story 28, 36).
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

use crate::debug::lockstep::LockstepOutcome;
use crate::debug::lockstep_fingerprint::{describe_part, Fingerprint};
use crate::gamehops::equivalence::smtrewrite::without_custom_smt_warning;
use crate::debug::lockstep_run::{run_lockstep_command, LockstepDebugOptions, LockstepSummary};
use crate::debug::progress::eprintln_above_bars;
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
use super::job::{
    create_if_absent, ensure_translation_files, is_proof_file, progress_dir, saved_tree_name,
    session_record_name, ClosedNode, LockError, LockstepRecord, OracleRecord, OracleStatus,
    ProofLock, SavedTree, SessionRecord, SessionRecordError,
};
use super::json::Goal;
use super::session::{split_sentences, Session, SessionError, SessionEvent, JSON_BRANCH};

pub use super::transcript::{EcTranscriptMode, GOALS_PER_STEP, GOAL_TEXT_CAP};
pub use live::{strip_timings, LiveConfig, LiveHandle};

pub use driver::{Admit, AdmitReason, DominoView, OracleStats, Timeouts};
use driver::{OracleTree, Prover, Resume, Sealed};

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
    #[error(transparent)]
    Record(#[from] SessionRecordError),
    #[error(transparent)]
    Lock(#[from] LockError),
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
    /// `prove --force` (story 35): discard the equivalence's session record and restart its
    /// proof from the skeleton, instead of skipping it. Never rewrites a translation file.
    pub force: bool,
    /// `prove --resume`: how an oracle the session record holds as `interrupted` is resumed.
    pub resume: ResumeMode,
    /// Whether the run says, on stderr, which translation files it wrote for each equivalence it
    /// proves (story 44). Off for `--progress none`, and in library use.
    pub announce_stages: bool,
}

/// How a proof job resumes an oracle the session record holds as `interrupted` (`--resume`,
/// ADR 0008). Done oracles are resumed as story 37 resumes them under every mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ResumeMode {
    /// Walk the saved joint tree; each closed node's goal is closed with `admit.` and its recorded
    /// script goes into the file, not checked again.
    #[default]
    Trust,
    /// As `trust`, but each closed node's recorded script is sent again; a rejected sentence
    /// makes the node be proved live.
    Replay,
    /// Prove the oracle from scratch, lockstep execution included.
    Restart,
}

impl ResumeMode {
    /// The mode as `--resume` spells it, and as the report and the page show it.
    pub fn slug(self) -> &'static str {
        match self {
            ResumeMode::Trust => "trust",
            ResumeMode::Replay => "replay",
            ResumeMode::Restart => "restart",
        }
    }
}

impl TacticsOptions {
    fn stop_requested(&self) -> bool {
        self.stop.as_ref().is_some_and(|s| s.load(Ordering::Relaxed))
    }
}

/// Where a Ctrl-C stopped a tactics run (story 34), or where a job ended early
/// ([`EquivalenceTactics::ended_early`]). Oracles finished before keep their scripts, oracles not
/// reached keep `+ proc; inline. admit.`.
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

/// The most times one proof job replaces an EasyCrypt that left an interrupt unanswered (a
/// **respawn**). The next unanswered interrupt ends the job, as a Ctrl-C would.
const MAX_RESPAWNS: usize = 2;

/// EasyCrypt left an interrupt unanswered while an oracle was proved: the oracle was sealed where
/// the walk stood, and EasyCrypt was respawned (or the job ended there).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unanswered {
    pub oracle: String,
    /// The joint node the walk was in, as the oracle's `interrupted` admits name it.
    pub node: String,
    /// How many `SIGINT`s went unanswered, and over how long.
    pub signals: usize,
    pub waited: Duration,
    /// How long starting a fresh EasyCrypt and opening the proof again took. `None`: there was
    /// no respawn, the job ended here ([`EquivalenceTactics::ended_early`]).
    pub respawn: Option<Duration>,
}

impl std::fmt::Display for Unanswered {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "EasyCrypt left an interrupt unanswered at {} ({} signals over {} s); oracle sealed, ",
            self.node,
            self.signals,
            self.waited.as_secs()
        )?;
        match self.respawn {
            Some(took) => write!(f, "EasyCrypt respawned (proof opened again in {})", secs(took)),
            None => write!(f, "EasyCrypt not respawned"),
        }
    }
}

/// The warning for an answer that shows EasyCrypt swallowed an interrupt, given at most once per
/// run ([`SwallowWatch`]). `head` is the start of the message that shows it.
fn swallow_warning(head: &str) -> String {
    format!(
        "EasyCrypt swallowed an interrupt (`{head}`). Rebuild it from branch \
         `{JSON_BRANCH}` (story `easycrypt-never-swallows-an-interrupt`); until then, \
         interrupted attempts can run far past their time and proof jobs may need respawns."
    )
}

/// Looks at every answer of a run for an interrupt EasyCrypt swallowed
/// ([`Response::swallowed_interrupt`](super::json::Response::swallowed_interrupt)) and warns on
/// stderr the first time. The answer itself is left as it is: `ok` and `error` are truthful about
/// EasyCrypt's state.
#[derive(Clone, Default)]
struct SwallowWatch(std::rc::Rc<std::cell::RefCell<Option<String>>>);

impl SwallowWatch {
    /// The warning, the first time an answer shows a swallowed interrupt; `None` after that.
    fn see(&self, response: &super::json::Response) -> Option<String> {
        if self.0.borrow().is_some() {
            return None;
        }
        let warning = swallow_warning(&response.swallowed_interrupt()?);
        *self.0.borrow_mut() = Some(warning.clone());
        Some(warning)
    }

    fn warning(&self) -> Option<String> {
        self.0.borrow().clone()
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
    /// After every sentence EasyCrypt accepts (story 38, the default): a `kill -9` loses at most
    /// the sentence in flight. Rejected, timed-out and interrupted sentences are never written.
    Tactic,
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
            write_granularity: WriteGranularity::Tactic,
            stop: None,
            force: false,
            resume: ResumeMode::Trust,
            announce_stages: false,
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
    /// The outermost closed nodes, for the session record of an interrupted oracle.
    pub closed: Vec<ClosedNode>,
    /// The [`SavedTree::id`] of the joint tree `closed` was proved on, when one was saved.
    pub tree_id: Option<String>,
    /// Not proved by this run: read back from the session record (story 37).
    pub resumed: bool,
    /// Walked again from the session record's closed nodes on the saved joint tree.
    pub resumed_at: Option<ResumedAt>,
}

/// Where an interrupted oracle was resumed, and with what (ADR 0008).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResumedAt {
    /// The in-flight node of the earlier job: `N<k>` or `router`.
    pub node: String,
    /// Closed nodes kept from the session record.
    pub kept: usize,
    /// How they were kept.
    pub mode: ResumeMode,
    /// What changed in the project since the tree was saved (fingerprint parts); empty when
    /// nothing did.
    pub stale: Vec<&'static str>,
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
            closed: Vec::new(),
            tree_id: None,
            resumed: false,
            resumed_at: None,
        }
    }

    /// The oracle as a session record holds it, or `None` when the record cannot be resumed
    /// from: not done, no script, or a reason or verdict this version does not know.
    fn from_record(record: &OracleRecord) -> Option<OracleTactics> {
        let script = record.script.clone().filter(|_| record.is_resumable())?;
        let admits = record
            .admits
            .iter()
            .map(Admit::from_record)
            .collect::<Option<Vec<_>>>()?;
        let lockstep = record.lockstep.unwrap_or(LockstepRecord {
            joint_paths: 0,
            ms: 0,
        });
        Some(OracleTactics {
            oracle: record.name.clone(),
            problem: None,
            stats: OracleStats {
                admits,
                ..OracleStats::default()
            },
            alignment_mismatches: vec![],
            joint_paths: lockstep.joint_paths,
            nodes: 0,
            stuck_points: 0,
            lockstep_time: Duration::from_millis(lockstep.ms),
            easycrypt_time: Duration::ZERO,
            script,
            closed: Vec::new(),
            tree_id: None,
            resumed: true,
            resumed_at: None,
        })
    }

    /// This oracle's entry in the session record.
    fn to_record(&self) -> OracleRecord {
        let interrupted = self
            .stats
            .admits
            .iter()
            .any(|a| a.reason == AdmitReason::Interrupted);
        let status = if interrupted {
            OracleStatus::Interrupted
        } else {
            OracleStatus::Done
        };
        OracleRecord {
            name: self.oracle.clone(),
            status,
            script: (status == OracleStatus::Done).then(|| self.script.clone()),
            admits: self.stats.admits.iter().map(Admit::to_record).collect(),
            lockstep: Some(LockstepRecord {
                joint_paths: self.joint_paths,
                ms: self.lockstep_time.as_millis() as u64,
            }),
            closed: if status == OracleStatus::Interrupted {
                self.closed.clone()
            } else {
                Vec::new()
            },
            tree_id: self.tree_id.clone().filter(|_| status == OracleStatus::Interrupted),
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
    /// The run was stopped by Ctrl-C while on this equivalence (story 34), or the job ended
    /// early ([`Self::ended_early`]): where.
    pub interrupted: Option<Interrupted>,
    /// Why the job ended before its last oracle although nobody pressed Ctrl-C: EasyCrypt left
    /// more interrupts unanswered than a job respawns it for, or a respawn failed.
    /// [`Self::interrupted`] says where.
    pub ended_early: Option<String>,
    /// Every interrupt EasyCrypt left unanswered in this job, in order.
    pub unanswered: Vec<Unanswered>,
    /// How many times the file was written, at the last write (story 38).
    pub writes: usize,
    /// This job's transcript, `progress/Eq_<L>_<R>/ec-transcript.jsonl` (story 36).
    pub transcript: PathBuf,
}

#[derive(Debug, Clone)]
pub struct TheoremTactics {
    pub theorem: String,
    pub equivalences: Vec<EquivalenceTactics>,
    pub elapsed: Duration,
    /// The warning given when an answer showed EasyCrypt swallowed an interrupt (once per run).
    pub swallowed_interrupt: Option<String>,
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
            .filter(|e| e.ended_early.is_none())
            .find_map(|e| e.interrupted.as_ref())
    }

    /// Whether a proof job ended before its last oracle without a Ctrl-C
    /// ([`EquivalenceTactics::ended_early`]).
    pub fn ended_early(&self) -> bool {
        self.equivalences.iter().any(|e| e.ended_early.is_some())
    }
}

/// The whole of `prove` for one exported theorem, already written to `out_dir`: rewrites
/// the selected `Eq_*.ec` files, writes their reports, and per equivalence its transcript and
/// live page (`progress/Eq_<L>_<R>/`), and returns what it did.
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
        &mut || Box::new(NopExportObserver),
    )
}

/// [`run_tactics`], reporting the `tactics` phase to an observer per equivalence (per oracle
/// and per goal): `progress` is called once for each equivalence that is proved.
///
/// Each selected equivalence is one **proof job** (story 36): it takes the lock of
/// `progress/Eq_<L>_<R>/` first, refusing if another live process holds it, and keeps its page
/// and transcript there, so jobs on different equivalences share nothing they write. The lock
/// is released when the equivalence ends, however it ends.
pub fn run_tactics_observed<P, B>(
    theorem: &Theorem<'_>,
    project: &P,
    exported: &ExportedTheorem,
    out_dir: &Path,
    backend: &B,
    options: &TacticsOptions,
    progress: &mut dyn FnMut() -> Box<dyn ExportObserver>,
) -> Result<TheoremTactics, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    std::fs::create_dir_all(out_dir)?;
    let out_dir = std::fs::canonicalize(out_dir).unwrap_or_else(|_| out_dir.to_path_buf());
    let started = Instant::now();
    let (theorem_ec, _aux) = EasyCryptTransform.transform_theorem(theorem)?;
    let swallow = SwallowWatch::default();

    let mut equivalences = Vec::new();
    for eq in &exported.equivalences {
        if options.proofstep.is_some_and(|p| p != eq.proofstep) {
            continue;
        }
        let stem = eq.proof_file.trim_end_matches(".ec").to_string();
        let dir = progress_dir(&out_dir, &stem);
        std::fs::create_dir_all(&dir)?;
        // before anything else (story 36 §3.2): one job per equivalence, and only for as long
        // as this equivalence takes, so a job on a later one is not blocked for the whole run
        let lock = ProofLock::acquire(&dir, &stem)?;
        // story 35: an equivalence that already has a session record is skipped, before
        // anything is created or truncated (its transcript and page stay)
        let prior = match plan_job(eq, &out_dir, options)? {
            JobPlan::Prove { prior } => prior,
            JobPlan::Skip => {
                drop(lock);
                let _ = std::fs::remove_dir(&dir); // only if the skip left it empty
                continue;
            }
        };
        // what translation owns: created if missing, never read or rewritten (ADR 0006)
        let created = ensure_translation_files(exported, &out_dir)?;
        let transcript_path = dir.join("ec-transcript.jsonl");
        // `None` once a capped write failed (story 31 §3.3)
        let mut transcript = Some(File::create(&transcript_path)?);
        let live = LiveHandle::new(LiveConfig {
            theorem: theorem.name.clone(),
            page: Some(dir.join("index.html")),
            transcript: transcript_path.clone(),
            translation: translation_line(exported, &created),
            progress: progress(),
        });
        let result = tactics_for_equivalence(
            theorem,
            &theorem_ec,
            project,
            exported,
            eq,
            &out_dir,
            &dir,
            &created,
            prior.as_ref(),
            backend,
            options,
            &mut transcript,
            &transcript_path,
            &live,
            &swallow,
        );
        // the last write always happens: the page on disk matches the end state
        match &result {
            Ok(tactics) => match (&tactics.interrupted, &tactics.ended_early) {
                (Some(at), Some(why)) => live.ended_early(&format!("{at}: {why}")),
                (Some(at), None) => live.interrupted(&at.to_string()),
                (None, _) => live.finish(),
            },
            Err(e) => live.fail(&e.to_string()),
        }
        drop(lock);
        let tactics = result?;
        // a job that ended early is not a stop: the next equivalence is a job of its own
        let interrupted = tactics.interrupted.is_some() && tactics.ended_early.is_none();
        equivalences.push(tactics);
        if interrupted {
            break;
        }
    }
    Ok(TheoremTactics {
        theorem: theorem.name.clone(),
        equivalences,
        elapsed: started.elapsed(),
        swallowed_interrupt: swallow.warning(),
    })
}

/// The one line the page shows in place of the export's phases: which translation files were
/// trusted and which this job created.
fn translation_line(exported: &ExportedTheorem, created: &[PathBuf]) -> String {
    let total = exported.files.keys().filter(|p| !is_proof_file(p)).count();
    if created.is_empty() {
        format!("translation files: all {total} present, trusted as they are")
    } else {
        let names: Vec<String> = created.iter().map(|p| p.display().to_string()).collect();
        format!(
            "translation files: {} of {total} present, trusted as they are; created: {}",
            total - created.len(),
            names.join(", ")
        )
    }
}

/// The stage line of an equivalence that is proved: what this process wrote of the translation
/// (the shared files it found missing and the equivalence's own `Eq_*.ec`), named when there are
/// fewer than [`NAMED_FILES_LIMIT`] and counted otherwise.
fn translation_files_line(stem: &str, wrote: &[String]) -> String {
    if wrote.is_empty() {
        format!("easycrypt prove: {stem} — translation files already on disk")
    } else if wrote.len() < NAMED_FILES_LIMIT {
        format!(
            "easycrypt prove: {stem} — wrote missing translation files: {}",
            wrote.join(", ")
        )
    } else {
        format!(
            "easycrypt prove: {stem} — wrote {} missing translation files",
            wrote.len()
        )
    }
}

/// A stage line names the files it wrote when fewer than this many.
const NAMED_FILES_LIMIT: usize = 6;

/// What a proof job does with an equivalence.
#[derive(Debug)]
enum JobPlan {
    /// Nothing: the record says it is proved (the reason is on stderr).
    Skip,
    /// Prove what is not done. `prior` is the record whose done oracles are resumed and whose
    /// other entries are kept (`None`: from scratch).
    Prove { prior: Option<SessionRecord> },
}

/// Decides what this proof job does for `eq` from its session record (story 37 §3.2), before
/// anything is created or truncated (its transcript and page stay when it skips).
///
/// | record | without `--force` | with `--force` |
/// |---|---|---|
/// | none | prove | prove |
/// | complete | skip | from scratch |
/// | partial | resume | from scratch |
///
/// With `--oracle O`: `O` done skips; with `--force`, `O` alone is re-proved and every other
/// entry is kept.
fn plan_job(
    eq: &EquivalenceReport,
    out_dir: &Path,
    options: &TacticsOptions,
) -> Result<JobPlan, TacticsError> {
    let record_path = out_dir.join(session_record_name(&eq.proof_file));
    let Some(mut record) = SessionRecord::read(&record_path)? else {
        return Ok(JobPlan::Prove { prior: None });
    };
    let file = &eq.proof_file;
    if options.force {
        let Some(oracle) = &options.oracle else {
            std::fs::remove_file(&record_path)?;
            return Ok(JobPlan::Prove { prior: None });
        };
        // this oracle alone is proved again: its entry goes, the others stay
        if let Some(entry) = record.oracles.iter_mut().find(|o| &o.name == oracle) {
            *entry = OracleRecord::new(oracle, OracleStatus::Pending);
        }
        record.complete = false;
        return Ok(JobPlan::Prove {
            prior: Some(record),
        });
    }
    let asked_done = options
        .oracle
        .as_ref()
        .map(|o| record.oracle(o).is_some_and(|e| e.status == OracleStatus::Done));
    if record.complete && asked_done.unwrap_or(true) {
        eprintln!("{}", record.skip_line(file));
        return Ok(JobPlan::Skip);
    }
    if let Some(oracle) = &options.oracle {
        if record.oracle(oracle).is_some_and(OracleRecord::is_resumable) {
            eprintln!(
                "skipping {oracle} of {}: already proved; --force re-proves it",
                file.trim_end_matches(".ec")
            );
            return Ok(JobPlan::Skip);
        }
    }
    if record.done_without_script() > 0 {
        eprintln!("{}", record.version_1_line(file));
    }
    eprintln!("{}", record.resume_line(file));
    Ok(JobPlan::Prove {
        prior: Some(record),
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
    progress_dir: &Path,
    created: &[PathBuf],
    prior: Option<&SessionRecord>,
    backend: &B,
    options: &TacticsOptions,
    transcript: &mut Option<File>,
    transcript_path: &Path,
    live: &LiveHandle,
    swallow: &SwallowWatch,
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

    // this equivalence's own file: created from the skeleton when missing, restarted from it
    // with `--force`; otherwise the run rewrites it at its first checkpoint
    let proof_path = out_dir.join(&file);
    let wrote_proof = if options.force && prior.is_none() {
        write_atomically(&proof_path, progress_dir, source)?;
        false // restarted from the skeleton, which is not a missing file
    } else {
        create_if_absent(&proof_path, source)?
    };
    if options.announce_stages {
        let mut wrote: Vec<String> = created.iter().map(|p| p.display().to_string()).collect();
        if wrote_proof {
            wrote.push(file.clone());
        }
        eprintln_above_bars(&translation_files_line(file.trim_end_matches(".ec"), &wrote));
    }
    // open the proof: everything up to `call (…); last first.`, then the base case
    let sentences = split_sentences(source);
    let call_prefix = sentences_until_call(&file, source)?;
    // oracles the session record has proved: not walked, not re-sent (ADR 0006)
    let resumed: Vec<OracleTactics> = setup
        .oracles
        .iter()
        .filter_map(|(name, _)| prior?.oracle(name).and_then(OracleTactics::from_record))
        .collect();
    let is_resumed = |name: &str| resumed.iter().any(|r| r.oracle == name);
    let selected_oracles: Vec<String> = setup
        .oracles
        .iter()
        .map(|(name, _)| name.clone())
        .filter(|name| selected(name) || is_resumed(name))
        .collect();
    live.equivalence_started(&file, eq.proofstep, &eq.left_name, &eq.right_name, &selected_oracles);
    let report_file = file.trim_end_matches(".ec").to_string() + ".report.txt";
    let mut proof = ProofFile {
        theorem: &theorem.name,
        source,
        procs: &setup.oracles,
        out_dir,
        progress_dir,
        prior,
        started,
        tactics: EquivalenceTactics {
            transcript: transcript_path.to_path_buf(),
            proofstep: eq.proofstep,
            proof_file: file.clone(),
            left: eq.left_name.clone(),
            right: eq.right_name.clone(),
            oracles: Vec::new(),
            base_case_admitted: false,
            elapsed: Duration::ZERO,
            report_file,
            interrupted: None,
            ended_early: None,
            unanswered: Vec::new(),
            writes: 0,
        },
        writes: std::cell::Cell::new(0),
    };
    // their scripts are in every write from the first one on, in the file's order
    for result in &resumed {
        live.oracle_finished(result);
        proof.tactics.oracles.push(result.clone());
    }
    let base = sentences.get(call_prefix.len()).map(String::as_str);
    let job = SessionSetup {
        out_dir,
        transcript_path,
        options,
        file: &file,
        live,
        swallow,
    };
    // Ctrl-C (story 34): the equivalence ends where it stands, with what is written
    let interrupted = 'run: {
        if options.stop_requested() {
            break 'run Some(Interrupted::NoOracleInFlight);
        }
        live.activity("starting EasyCrypt and opening the proof");
        let mut session = job.start(transcript.as_ref(), None)?;
        match open_proof(&mut session, &call_prefix, base, false, &file, options)? {
            Opened::Stopped => break 'run Some(Interrupted::NoOracleInFlight),
            Opened::Open { base_case_admitted } => {
                proof.tactics.base_case_admitted = base_case_admitted;
            }
        }

        let mut interrupted = None;
        while let Some(goal) = session.goals().first() {
            if options.stop_requested() {
                interrupted = Some(Interrupted::NoOracleInFlight);
                break;
            }
            let target = setup.oracle_of_goal(goal);
            let in_file = |name: &str| proof.tactics.oracles.iter().any(|o| o.oracle == name);
            if target.as_deref().is_some_and(in_file) {
                // proved in an earlier session or before a respawn, and its script is in the
                // file already
                session.send("admit.")?;
                continue;
            }
            match target.filter(|o| selected(o)) {
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
                    let (result, stopped, unanswered) = match end {
                        OracleEnd::Done(result) => (Some(result), None, None),
                        OracleEnd::Stopped { sealed, at } => (sealed, Some(at), None),
                        OracleEnd::Unanswered { sealed, unanswered } => {
                            (Some(sealed), None, Some(unanswered))
                        }
                    };
                    if let Some(u) = &unanswered {
                        proof.tactics.unanswered.push(u.clone());
                    }
                    if let Some(result) = result {
                        proof.tactics.oracles.push(result);
                        proof.write(None)?;
                        live.oracle_finished(proof.tactics.oracles.last().expect("just pushed"));
                    }
                    if stopped.is_some() {
                        interrupted = stopped;
                        break;
                    }
                    if unanswered.is_some() {
                        // the oracle is sealed and written; the session is lost
                        if session.transcript_dropped() {
                            *transcript = None;
                        }
                        let respawned = respawn(
                            session,
                            &job,
                            transcript.as_ref(),
                            &call_prefix,
                            base,
                            &mut proof.tactics,
                        );
                        match respawned {
                            Ok(fresh) => session = fresh,
                            // the job ends here, its transcript checked above
                            Err(at) => break 'run Some(at),
                        }
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

/// What every EasyCrypt of a proof job is started with: the first one and each respawn.
struct SessionSetup<'a> {
    /// The theorem's output directory: EasyCrypt's working directory and `-I`.
    out_dir: &'a Path,
    transcript_path: &'a Path,
    options: &'a TacticsOptions,
    /// The proof file, the tag of every transcript record.
    file: &'a str,
    live: &'a LiveHandle,
    swallow: &'a SwallowWatch,
}

impl SessionSetup<'_> {
    /// A fresh EasyCrypt for the job. Its records are appended to the job's transcript
    /// (`transcript`; `None`: dropped after a failed write), tagged with the proof file and, for
    /// the `n`th respawn, `(respawn n)`. Its answers go to the live page and are watched for a
    /// swallowed interrupt. The per-sentence timeout and the stop flag are set.
    fn start(&self, transcript: Option<&File>, respawn: Option<usize>) -> Result<Session, TacticsError> {
        let mut session = spawn_easycrypt(self.out_dir)?;
        if let Some(transcript) = transcript {
            let tag = match respawn {
                None => self.file.to_string(),
                Some(n) => format!("{} (respawn {n})", self.file),
            };
            // a clone shares the file's offset: the records of every session follow each other
            session.set_transcript_sink(
                Box::new(transcript.try_clone()?),
                self.transcript_path,
                self.options.ec_transcript,
                &tag,
            );
        }
        let mut page = self.live.session_observer();
        let swallow = self.swallow.clone();
        session.set_observer(Box::new(move |event| {
            if let SessionEvent::Answered { response, .. } = event {
                if let Some(warning) = swallow.see(response) {
                    eprintln_above_bars(&format!("warning: {warning}"));
                }
            }
            page(event);
        }));
        session.set_timeout(self.options.ec_timeout);
        if let Some(stop) = &self.options.stop {
            session.set_stop(stop.clone());
        }
        Ok(session)
    }
}

/// [`Session::start`]; in a test that set [`tests::TEST_EASYCRYPT`], that EasyCrypt with its
/// interrupt timing.
fn spawn_easycrypt(dir: &Path) -> Result<Session, SessionError> {
    #[cfg(test)]
    if let Some(fake) = tests::TEST_EASYCRYPT.with(|t| t.borrow().clone()) {
        let mut session = Session::start_with(&fake.binary, dir)?;
        session.set_interrupt_timing(fake.grace, fake.resend);
        return Ok(session);
    }
    Session::start(dir)
}

/// How opening the proof ended.
enum Opened {
    /// The oracles' goals are in front. `base_case_admitted`: the base case did not close.
    Open { base_case_admitted: bool },
    /// The run was asked to stop (Ctrl-C) on the way.
    Stopped,
}

/// Opens the proof in a fresh session: every sentence up to `call (…); last first.`, then the
/// base case `base`. `admitted`: an earlier session of the job admitted the base case, so it is
/// admitted again without being tried.
fn open_proof(
    session: &mut Session,
    call_prefix: &[String],
    base: Option<&str>,
    admitted: bool,
    file: &str,
    options: &TacticsOptions,
) -> Result<Opened, TacticsError> {
    for sentence in call_prefix {
        let response = session.send(sentence)?;
        if options.stop_requested() {
            return Ok(Opened::Stopped);
        }
        ok_or_reject(response, file, sentence)?;
    }
    let Some(base) = base else {
        return Ok(Opened::Open {
            base_case_admitted: false,
        });
    };
    if !admitted && session.send(base)?.status == super::json::Status::Ok {
        return Ok(Opened::Open {
            base_case_admitted: false,
        });
    }
    if options.stop_requested() {
        return Ok(Opened::Stopped);
    }
    session.send("admit.")?;
    Ok(Opened::Open {
        base_case_admitted: true,
    })
}

/// Replaces `old`, the EasyCrypt that left the interrupt of `tactics.unanswered`'s last entry
/// unanswered, with a fresh one opened at the same proof (a **respawn**). The oracle in flight
/// is sealed and in `tactics.oracles` already; the goal loop closes it, and every oracle before
/// it, with `admit.`.
///
/// `Err` is where the job ends instead: after [`MAX_RESPAWNS`] respawns, or when the respawn
/// fails, with the sealed oracle and [`EquivalenceTactics::ended_early`]; on a Ctrl-C, as a
/// Ctrl-C.
fn respawn(
    old: Session,
    job: &SessionSetup<'_>,
    transcript: Option<&File>,
    call_prefix: &[String],
    base: Option<&str>,
    tactics: &mut EquivalenceTactics,
) -> Result<Session, Interrupted> {
    // `Drop` kills the child without waiting on it: it may be stuck in a prover
    drop(old);
    let respawns = tactics.unanswered.len() - 1;
    let last = tactics.unanswered.last().expect("an unanswered interrupt").clone();
    let sealed = Interrupted::Sealed {
        admits: tactics
            .oracles
            .iter()
            .filter(|o| o.oracle == last.oracle)
            .flat_map(|o| o.stats.admits.iter())
            .filter(|a| a.reason == AdmitReason::Interrupted)
            .count(),
        oracle: last.oracle.clone(),
        node: last.node.clone(),
    };
    let fresh = 'fresh: {
        if respawns == MAX_RESPAWNS {
            tactics.ended_early = Some(format!(
                "EasyCrypt left {} interrupts unanswered, and a proof job respawns it at most \
                 {MAX_RESPAWNS} times",
                respawns + 1
            ));
            break 'fresh Err(sealed);
        }
        if job.options.stop_requested() {
            break 'fresh Err(Interrupted::NoOracleInFlight);
        }
        let began = Instant::now();
        job.live
            .activity("respawning EasyCrypt and opening the proof again");
        let opened = job.start(transcript, Some(respawns + 1)).and_then(|mut session| {
            let admitted = tactics.base_case_admitted;
            let opened = open_proof(&mut session, call_prefix, base, admitted, job.file, job.options)?;
            Ok((session, opened))
        });
        match opened {
            Ok((session, Opened::Open { base_case_admitted })) => {
                tactics.base_case_admitted |= base_case_admitted;
                if let Some(u) = tactics.unanswered.last_mut() {
                    u.respawn = Some(began.elapsed());
                }
                Ok(session)
            }
            Ok((_, Opened::Stopped)) => Err(Interrupted::NoOracleInFlight),
            Err(_) if job.options.stop_requested() => Err(Interrupted::NoOracleInFlight),
            Err(e) => {
                tactics.ended_early = Some(format!("respawning EasyCrypt failed: {e}"));
                Err(sealed)
            }
        }
    };
    job.live
        .unanswered(tactics.unanswered.last().expect("an unanswered interrupt"));
    fresh
}

/// Where lockstep execution of `oracle` writes its artifacts: beside the export it describes,
/// under the theorem it belongs to (story 19 §4.6). `domino easycrypt debug` writes there too.
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
    /// The theorem's name, for the session record.
    theorem: &'a str,
    /// The exported file: every oracle `+ proc; inline. admit.`.
    source: &'a str,
    /// The record this run resumes: its entries for oracles this run does not prove stay.
    prior: Option<&'a SessionRecord>,
    /// `(exported name, EasyCrypt's procedure name)` of every oracle, in the file's order.
    procs: &'a [(String, String)],
    /// The theorem's output directory: the file, the report and the record.
    out_dir: &'a Path,
    /// This equivalence's `progress/Eq_<L>_<R>/`, for the temporary files (story 36).
    progress_dir: &'a Path,
    /// When the equivalence started: the report's elapsed time.
    started: Instant,
    /// The equivalence so far: its finished oracles, in the order they finished.
    tactics: EquivalenceTactics,
    /// How many times [`Self::write`] has written (story 38).
    writes: std::cell::Cell<usize>,
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
        self.writes.set(self.writes.get() + 1);
        now.writes = self.writes.get();
        // the report first: a reader who sees the file finds a report at least as new
        let tmp_dir = self.progress_dir;
        write_atomically(&self.out_dir.join(&now.report_file), tmp_dir, &now.render())?;
        write_atomically(
            &self.out_dir.join(&now.proof_file),
            tmp_dir,
            &self.text(&now.oracles),
        )?;
        // the record last (story 35 §3.4): a crash between the two leaves a record that claims
        // less than the file holds, which costs a re-proof and never claims a missing proof
        let record = self.record(&now);
        if record.oracles.iter().any(|o| o.status != OracleStatus::Pending) {
            write_atomically(
                &self.out_dir.join(session_record_name(&now.proof_file)),
                tmp_dir,
                &record.to_json(),
            )?;
        }
        Ok(now)
    }

    /// The session record of `now`: every exported oracle's entry, in the file's order. An
    /// oracle this run has not got to keeps the entry it had.
    fn record(&self, now: &EquivalenceTactics) -> SessionRecord {
        let oracles = self
            .procs
            .iter()
            .map(|(name, _)| match now.oracles.iter().find(|o| &o.oracle == name) {
                Some(o) => o.to_record(),
                None => self
                    .prior
                    .and_then(|p| p.oracle(name))
                    .cloned()
                    .unwrap_or_else(|| OracleRecord::new(name, OracleStatus::Pending)),
            })
            .collect();
        SessionRecord::new(self.theorem, &now.left, &now.right, oracles)
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
/// It is in the job's own `progress/Eq_<L>_<R>/`, a run artifact (story 32), so a leftover one
/// blocks nothing and no other job's temporary file can have the same path.
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
    /// EasyCrypt left an interrupt unanswered: the oracle is `sealed` where the walk stood, and
    /// the session cannot be used any more.
    Unanswered {
        sealed: OracleTactics,
        unanswered: Unanswered,
    },
}

/// The joint tree one oracle's walk follows: lockstep execution's, fresh or saved.
struct WalkedTree {
    outcome: LockstepOutcome,
    summary: LockstepSummary,
    /// The names of the loaded state relations (`Domino_<name>` is unfolded).
    relations: Vec<String>,
    /// What lockstep execution took (in the earlier job, for a saved tree).
    lockstep_time: Duration,
    /// Its [`SavedTree::id`]; `None` when it could not be saved.
    id: Option<String>,
}

/// What resuming an interrupted oracle starts from, besides its saved tree.
struct ResumeFrom {
    closed: Vec<ClosedNode>,
    /// The earlier job's in-flight node: `N<k>` or `router`.
    in_flight: String,
    mode: ResumeMode,
    /// What changed since the tree was saved ([`ResumedAt::stale`]).
    stale: Vec<&'static str>,
}

struct Resuming {
    tree: WalkedTree,
    from: ResumeFrom,
}

/// How [`lockstep`] ended.
enum Lockstep {
    /// With a joint tree to walk, saved beside the session record.
    Walk(WalkedTree),
    /// Without: the oracle ends here.
    Ended(OracleEnd),
}

/// The saved joint tree and closed nodes to resume `oracle` from, when the session record holds
/// it as `interrupted` and `--resume` is not `restart` (ADR 0008). `None`, with a warning when
/// the oracle cannot be resumed, means it is proved from scratch.
fn resuming<P: Project>(
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    oracle: &str,
    proof: &ProofFile<'_>,
    options: &TacticsOptions,
) -> Option<Resuming> {
    let prior = proof.prior?;
    let entry = prior
        .oracle(oracle)
        .filter(|e| e.status == OracleStatus::Interrupted)?;
    if options.resume == ResumeMode::Restart {
        return None;
    }
    let restart = |why: &str| {
        eprintln_above_bars(&format!("warning: {why}; {oracle} is proved again from the start"));
    };
    if prior.version < 3 {
        restart(&format!(
            "the session record of {} has no closed nodes (version {})",
            eq.proof_file.trim_end_matches(".ec"),
            prior.version
        ));
        return None;
    }
    let path = proof.out_dir.join(saved_tree_name(&eq.proof_file, oracle));
    let saved = match SavedTree::read(&path) {
        Ok(Some(saved)) if saved.oracle == oracle => saved,
        Ok(Some(saved)) => {
            restart(&format!("{} holds the tree of {}", path.display(), saved.oracle));
            return None;
        }
        Ok(None) => {
            restart(&format!("{oracle} has no saved joint tree"));
            return None;
        }
        Err(e) => {
            restart(&e.to_string());
            return None;
        }
    };
    // a later lockstep execution (`--resume restart`, or a fallback) rewrites the tree before
    // the record: a job killed in between leaves closed nodes proved on another tree
    if entry.tree_id.as_deref() != Some(saved.id.as_str()) {
        restart(&format!(
            "the saved joint tree of {oracle} is not the one its closed nodes were proved on"
        ));
        return None;
    }
    let stale = match Fingerprint::of(project, theorem, eq.proofstep, oracle) {
        Ok(now) if now.hex == saved.fingerprint => Vec::new(),
        Ok(now) => {
            let changed = now.changed_from(&saved.fingerprint_parts);
            if changed.is_empty() {
                vec!["the project"]
            } else {
                changed
            }
        }
        Err(_) => vec!["the project"],
    };
    if !stale.is_empty() {
        let what: Vec<&str> = stale.iter().map(|p| describe_part(p)).collect();
        eprintln_above_bars(&format!(
            "warning: the saved joint tree of {oracle} predates changes to {}; the EasyCrypt \
             files may be stale too. Export with --force to start over.",
            what.join(", ")
        ));
    }
    let lockstep_time = Duration::from_millis(entry.lockstep.map_or(0, |l| l.ms));
    Some(Resuming {
        from: ResumeFrom {
            closed: entry.closed.clone(),
            in_flight: entry.in_flight().unwrap_or("router").to_string(),
            mode: options.resume,
            stale,
        },
        tree: WalkedTree {
            outcome: saved.outcome,
            summary: saved.summary,
            relations: saved.relations,
            lockstep_time,
            id: Some(saved.id),
        },
    })
}

/// Lockstep execution of `oracle`, its joint tree saved beside the session record before the
/// first sentence is sent. Its artifacts are written exactly as `domino easycrypt debug` writes
/// them, so every `S`/`J` of an admit has a page to open.
#[allow(clippy::too_many_arguments)]
fn lockstep<P, B>(
    session: &mut Session,
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    oracle: &str,
    backend: &B,
    options: &TacticsOptions,
    live: &LiveHandle,
    proof: &ProofFile<'_>,
) -> Result<Lockstep, TacticsError>
where
    P: Project,
    B: SmtSolverBackend,
{
    let lockstep_started = Instant::now();
    live.activity("lockstep execution");
    live.lockstep_started(oracle);
    let mut lockstep_observer = live.lockstep_observer();
    let run = run_lockstep_command(
        project,
        &theorem.name,
        eq.proofstep,
        oracle,
        &LockstepDebugOptions::easycrypt(options.lockstep_timeout_ms),
        backend,
        // next to the export it describes: `<out>/<theorem>/!debug!/<left>-<right>/<oracle>/`
        Some(debug_dir(proof.out_dir, &eq.left_name, &eq.right_name, oracle)),
        lockstep_observer.as_mut(),
        options.stop.as_deref(),
    );
    // its bars go before the summary line is printed
    drop(lockstep_observer);
    let lockstep_time = lockstep_started.elapsed();
    live.lockstep_finished(
        oracle,
        run.as_ref().ok().map(|r| (r.summary.joint_paths, r.summary.stuck_points)),
        lockstep_time,
        options.stop_requested(),
    );
    live.activity("");
    if options.stop_requested() {
        // lockstep execution was stopped, or has just finished: nothing was sent
        return Ok(Lockstep::Ended(OracleEnd::Stopped {
            sealed: None,
            at: Interrupted::Lockstep {
                oracle: oracle.to_string(),
            },
        }));
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
            return Ok(Lockstep::Ended(OracleEnd::Done(result)));
        }
    };
    let mut tree = WalkedTree {
        outcome: run.outcome,
        summary: run.summary,
        relations: run.meta.goals.relations.iter().map(|r| r.name.clone()).collect(),
        lockstep_time,
        id: None,
    };
    tree.id = save_tree(project, theorem, eq, oracle, proof, &tree)?;
    Ok(Lockstep::Walk(tree))
}

/// Writes `Eq_<L>_<R>.<oracle>.tree.json`, atomically, replacing any earlier one, and returns
/// its [`SavedTree::id`]. Without a fingerprint there is no tree to trust later: an earlier one
/// is removed, with a warning, and there is no id.
fn save_tree<P: Project>(
    project: &P,
    theorem: &Theorem<'_>,
    eq: &EquivalenceReport,
    oracle: &str,
    proof: &ProofFile<'_>,
    tree: &WalkedTree,
) -> std::io::Result<Option<String>> {
    let path = proof.out_dir.join(saved_tree_name(&eq.proof_file, oracle));
    // lockstep execution has just loaded the invariant files, and warned
    let fingerprint = without_custom_smt_warning(|| {
        Fingerprint::of(project, theorem, eq.proofstep, oracle)
    });
    let fingerprint = match fingerprint {
        Ok(fingerprint) => fingerprint,
        Err(e) => {
            eprintln_above_bars(&format!(
                "warning: the joint tree of {oracle} is not saved, its fingerprint failed: {e}; \
                 an interrupted {oracle} will be proved again from the start"
            ));
            return match std::fs::remove_file(&path) {
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(e),
                _ => Ok(None),
            };
        }
    };
    // `SavedTree` owns what it holds; the walk keeps its own copy
    let saved = SavedTree {
        version: SavedTree::VERSION,
        oracle: oracle.to_string(),
        id: SavedTree::new_id(),
        domino: env!("CARGO_PKG_VERSION").to_string(),
        fingerprint: fingerprint.hex,
        fingerprint_parts: fingerprint.parts,
        outcome: tree.outcome.clone(),
        summary: tree.summary.clone(),
        relations: tree.relations.clone(),
    };
    write_atomically(&path, proof.progress_dir, &saved.to_json())?;
    Ok(Some(saved.id))
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
    // an interrupted oracle of the session record: its saved joint tree, no lockstep execution
    let (walked, resume_from) = match resuming(project, theorem, eq, oracle, proof, options) {
        Some(Resuming { tree, from }) => {
            live.oracle_resumed(&from.in_flight, from.mode.slug());
            let dir = debug_dir(proof.out_dir, &eq.left_name, &eq.right_name, oracle);
            if dir.join("index.html").exists() {
                live.lockstep_done(&dir);
            }
            (tree, Some(from))
        }
        None => match lockstep(session, project, theorem, eq, oracle, backend, options, live, proof)? {
            Lockstep::Walk(tree) => (tree, None),
            Lockstep::Ended(end) => return Ok(end),
        },
    };
    let lockstep_time = walked.lockstep_time;

    let tree = OracleTree::new(&walked.outcome);
    let resume = resume_from.as_ref().map(|from| {
        Resume::new(&tree, from.mode, from.closed.clone(), &from.in_flight)
    });
    // the operators `inv` unfolds to, by name (`writers::easycrypt::invariant`)
    let unfold_ops: Vec<String> = ["inv".to_string(), "params_inv".to_string()]
        .into_iter()
        .chain(walked.relations.iter().map(|r| format!("Domino_{r}")))
        .collect();
    let left_ir = inline_oracle_ec(setup.left_inst, oracle)?;
    let right_ir = inline_oracle_ec(setup.right_inst, oracle)?;
    let began = Instant::now();
    let resumed_at = |kept: usize| {
        resume_from.as_ref().map(|from| ResumedAt {
            node: from.in_flight.clone(),
            kept,
            mode: from.mode,
            stale: from.stale.clone(),
        })
    };
    let result_of = |sealed: Sealed| OracleTactics {
        oracle: oracle.to_string(),
        problem: None,
        stats: sealed.stats,
        alignment_mismatches: sealed.mismatches,
        joint_paths: walked.summary.joint_paths,
        nodes: walked.summary.nodes,
        stuck_points: walked.summary.stuck_points,
        lockstep_time,
        easycrypt_time: began.elapsed(),
        script: sealed.script,
        closed: sealed.closed,
        tree_id: walked.id.clone(),
        resumed: false,
        resumed_at: resumed_at(sealed.kept),
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
            WriteGranularity::Node | WriteGranularity::Tactic => Some(&mut write_sealed),
        },
        per_sentence: options.write_granularity == WriteGranularity::Tactic,
        node: None,
        mismatches: Vec::new(),
        stopped: None,
        resume,
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
    let (stopped, unanswered) = match proved {
        Ok(()) => (None, None),
        Err(SessionError::Stopped) => (
            Some(
                prover
                    .stopped
                    .take()
                    .expect("the walk seals the oracle before it stops"),
            ),
            None,
        ),
        // the walk sealed the oracle where it stood (`Prover::session_failed`)
        Err(SessionError::Unresponsive {
            signals, waited, ..
        }) if prover.stopped.is_some() => {
            let sealed = prover.stopped.take().expect("checked by the guard");
            let unanswered = Unanswered {
                oracle: oracle.to_string(),
                node: sealed.node.clone(),
                signals,
                waited,
                respawn: None,
            };
            (Some(sealed), Some(unanswered))
        }
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
    if let Some(unanswered) = unanswered {
        return Ok(OracleEnd::Unanswered {
            sealed: result,
            unanswered,
        });
    }
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
            if o.resumed {
                let _ = writeln!(
                    out,
                    "  {}: resumed from session record (lockstep {} joint paths, {} admits)",
                    o.oracle,
                    o.joint_paths,
                    o.stats.admits.len()
                );
                for a in &o.stats.admits {
                    let _ = writeln!(
                        out,
                        "    admit {} {} [{}] Domino: {}",
                        a.id,
                        a.claim,
                        a.reason.slug(),
                        a.domino.slug()
                    );
                }
                continue;
            }
            if let Some(problem) = &o.problem {
                let _ = writeln!(out, "  {}: no tactics ({problem})", o.oracle);
                continue;
            }
            if let Some(at) = &o.resumed_at {
                let _ = write!(
                    out,
                    "  {}: resumed at {} ({} closed node{} kept, {})",
                    o.oracle,
                    at.node,
                    at.kept,
                    if at.kept == 1 { "" } else { "s" },
                    at.mode.slug()
                );
                if !at.stale.is_empty() {
                    let _ = write!(out, "; saved joint tree is stale ({})", at.stale.join(", "));
                }
                out.push('\n');
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
            for u in self.unanswered.iter().filter(|u| u.oracle == o.oracle) {
                let _ = writeln!(out, "    {u}");
            }
        }
        match (&self.interrupted, &self.ended_early) {
            (Some(at), Some(why)) => {
                let _ = writeln!(out, "ended early: {at}: {why}");
            }
            (Some(at), None) => {
                let _ = writeln!(out, "interrupted: {at}");
            }
            (None, _) => {}
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
        for eq in &self.equivalences {
            let _ = writeln!(out, "transcript: {}", eq.transcript.display());
        }
        if let Some(warning) = &self.swallowed_interrupt {
            let _ = writeln!(out, "warning: {warning}");
        }
        let _ = writeln!(out, "elapsed: {}", secs(self.elapsed));
        out
    }
}

#[cfg(test)]
mod tests;
