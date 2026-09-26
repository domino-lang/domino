// SPDX-License-Identifier: MIT OR Apache-2.0

//! The live translation page of `domino easycrypt prove` (story 28).
//!
//! [`LiveHandle`] is the one observer of a `prove` run. It sees two streams:
//!
//! - the **session's**: every sentence about to run, a tick while it runs, its answer
//!   ([`SessionEvent`]);
//! - the **prover's**: which joint node it is working on, which ladder rung it tries, which
//!   `admit` it wrote.
//!
//! From them it keeps a small model (equivalences, oracles, the goal tree, the steps of each
//! goal) and rewrites `progress/Eq_<L>_<R>/index.html` after every answer, at most twice a second, always
//! once more at the end ([`LiveHandle::finish`], [`LiveHandle::fail`]). The page is a
//! self-contained file with a `<meta http-equiv="refresh">` while the run goes on.
//!
//! **What is embedded.** A step keeps its sentence, status, EasyCrypt's error text and messages
//! (all small). The `pp` of the goals a step left is not kept: the transcript
//! (`ec-transcript.jsonl` beside the page, one record per sentence) already holds it, and the model remembers
//! where each record is (byte offset and length). When the page is written, the goal text of the
//! *shown* steps only is read back from there, once per step: the step EasyCrypt is working on
//! (the goals it was applied to), the steps of the goal being worked on, and the last step of
//! each goal. Each goal's text is cut at [`GOAL_TEXT_CAP`] characters and at most
//! [`GOALS_PER_STEP`] goals are embedded per step; the cut says where the rest is. The capped
//! transcript (story 31) holds exactly this much of each answer, and says what it cut, so the
//! page is the same whichever `--ec-transcript` mode wrote the transcript. A step with no record
//! (the capped transcript was dropped after a failed write) has no goal text. So the page
//! grows with the number of goals (nodes), not with the number of sentences or with the size of
//! the goals, and the transcript is never embedded whole.
//!
//! **Timings** (a step's `ms`, the elapsed time, the pending command's age) are in one element,
//! `<script id="timings">`, and nowhere else: two runs of an unchanged project write the same
//! page once [`strip_timings`] has removed it.
//!
//! Nothing here changes what the prover sends or writes; every failure to write the page is
//! ignored (a page is a convenience, not a result).

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::{Duration, Instant};

mod page;

use serde_derive::Deserialize;

use crate::easycrypt::json::Status;
use crate::easycrypt::session::SessionEvent;
use crate::easycrypt::transcript::{GOALS_PER_STEP, GOAL_TEXT_CAP};
use crate::writers::easycrypt::progress::{ExportEvent, ExportObserver, ExportPhase};

use super::driver::Admit;
use super::{EquivalenceTactics, OracleTactics};

/// The most steps of the goal being worked on that are embedded (the newest).
const CURRENT_STEPS_SHOWN: usize = 12;
/// The most characters of an error or message kept per step.
const MESSAGE_CAP: usize = 2_000;
/// The pages are rewritten at most this often (twice a second).
const FLUSH_GAP: Duration = Duration::from_millis(500);
/// The most `J`/`S` ids listed on a node.
const IDS_PER_NODE: usize = 6;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StepStatus {
    Accepted,
    Failed,
    /// Interrupted by `--ec-timeout`.
    TimedOut,
    /// Interrupted because the run was asked to stop (Ctrl-C, story 34).
    Interrupted,
}

/// Where a step's record is in `ec-transcript.jsonl`.
#[derive(Debug, Clone, Copy)]
pub(super) struct RecordSpan {
    /// Number of the record, from 0: `sed -n <line+1>p`.
    pub line: usize,
    pub offset: u64,
    pub len: usize,
}

#[derive(Debug, Clone)]
pub(super) struct Step {
    /// `None` when no record was written for it (the transcript was dropped).
    pub record: Option<RecordSpan>,
    pub sentence: String,
    pub status: StepStatus,
    /// Accepted, and later undone (by `undo N.` in the session).
    pub undone: bool,
    pub is_undo: bool,
    pub error: Option<String>,
    pub messages: Vec<String>,
    pub ms: u64,
    /// The depth the session was at after this sentence.
    pub state: u64,
    pub goals_left: usize,
}

#[derive(Debug, Clone)]
pub(super) struct AdmitRec {
    /// The comment written after the `admit.` in the `.ec` file.
    pub label: String,
    pub id: String,
    pub reason: &'static str,
}

#[derive(Debug, Clone)]
pub(super) struct NodeRec {
    pub label: String,
    pub kind: String,
    pub ids: Vec<String>,
    pub more_ids: usize,
    /// The node of the lockstep page this goal is (`#n=<node>`).
    pub lockstep_node: Option<usize>,
    pub children: Vec<usize>,
    pub steps: Vec<usize>,
    pub rungs: Vec<String>,
    pub admits: Vec<AdmitRec>,
    pub done: bool,
}

#[derive(Debug, Clone, Default)]
pub(super) struct OracleSummary {
    pub closed: usize,
    pub fallbacks: usize,
    pub undone: usize,
    pub admits: Vec<(&'static str, usize)>,
    pub admit_total: usize,
    pub ec_ms: u64,
    pub problem: Option<String>,
    pub alignment_mismatches: usize,
    pub joint_paths: usize,
    pub nodes: usize,
    pub stuck_points: usize,
}

#[derive(Debug, Clone)]
pub(super) struct OracleRec {
    pub name: String,
    pub nodes: Vec<NodeRec>,
    pub roots: Vec<usize>,
    /// Relative link to the lockstep page of this oracle.
    pub lockstep_href: Option<String>,
    pub summary: Option<OracleSummary>,
    pub started: bool,
}

#[derive(Debug, Clone)]
pub(super) struct EqRec {
    pub file: String,
    pub proofstep: usize,
    pub left: String,
    pub right: String,
    pub oracles: Vec<OracleRec>,
    /// Sentences outside any oracle: the proof's opening, the base case, goals not asked for.
    pub setup_steps: usize,
    pub base_case_admitted: bool,
    pub report_file: Option<String>,
    pub finished: bool,
}

#[derive(Debug, Clone)]
pub(super) struct Pending {
    pub sentence: String,
    pub since: Instant,
    /// The step whose answer holds the goals this sentence is applied to.
    pub before: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RunState {
    Running,
    Done,
    Failed(String),
    /// Stopped by Ctrl-C (story 34): what was sealed, as the report says it.
    Interrupted(String),
}

/// The goal text embedded for one step.
#[derive(Debug, Clone, Default)]
pub(super) struct GoalTexts {
    pub goals: Vec<String>,
    /// How many goals the answer held (more than `goals` when cut).
    pub total: usize,
    /// Characters cut off the end of a goal, by goal.
    pub cut: Vec<usize>,
    pub unreadable: bool,
}

pub(super) struct Live {
    pub theorem: String,
    pub page: Option<PathBuf>,
    pub page_dir: PathBuf,
    pub transcript: PathBuf,
    pub translation: String,
    pub started: Instant,
    pub state: RunState,
    pub steps: Vec<Step>,
    pub eqs: Vec<EqRec>,
    /// The equivalence and oracle being worked on.
    pub cur_eq: Option<usize>,
    pub cur_oracle: Option<usize>,
    /// The nodes entered and not left yet, innermost last.
    pub node_stack: Vec<usize>,
    pub pending: Option<Pending>,
    /// What the run is doing when no goal is being worked on (`lockstep execution`, …).
    pub activity: String,
    pub last_answered: Option<usize>,
    /// Accepted, not undone steps of the current session, oldest first.
    live_steps: Vec<usize>,
    offset: u64,
    lines: usize,
    last_flush: Option<Instant>,
    flush_gap: Duration,
    progress: Box<dyn ExportObserver>,
    oracle_index: usize,
    oracle_total: usize,
    texts: HashMap<usize, GoalTexts>,
}

/// What `run_tactics` builds a [`LiveHandle`] from.
pub struct LiveConfig {
    pub theorem: String,
    /// `progress/Eq_<L>_<R>/index.html`; `None` keeps the model but writes nothing (tests).
    pub page: Option<PathBuf>,
    pub transcript: PathBuf,
    /// One line: which translation files were trusted and which the job created (story 36).
    pub translation: String,
    pub progress: Box<dyn ExportObserver>,
}

/// Shared between the session's observer and the prover.
#[derive(Clone)]
pub struct LiveHandle(Rc<RefCell<Live>>);

impl LiveHandle {
    pub fn new(config: LiveConfig) -> LiveHandle {
        let page_dir = config
            .page
            .as_deref()
            .and_then(Path::parent)
            .map(Path::to_path_buf)
            .unwrap_or_default();
        let live = Live {
            theorem: config.theorem,
            page: config.page,
            page_dir,
            transcript: config.transcript,
            translation: config.translation,
            started: Instant::now(),
            state: RunState::Running,
            steps: Vec::new(),
            eqs: Vec::new(),
            cur_eq: None,
            cur_oracle: None,
            node_stack: Vec::new(),
            pending: None,
            activity: String::new(),
            last_answered: None,
            live_steps: Vec::new(),
            offset: 0,
            lines: 0,
            last_flush: None,
            flush_gap: FLUSH_GAP,
            progress: config.progress,
            oracle_index: 0,
            oracle_total: 0,
            texts: HashMap::new(),
        };
        let handle = LiveHandle(Rc::new(RefCell::new(live)));
        handle.0.borrow_mut().touch(true);
        handle
    }

    /// The observer to give [`Session::set_observer`](crate::easycrypt::session::Session::set_observer).
    pub fn session_observer(&self) -> Box<dyn FnMut(&SessionEvent<'_>)> {
        let live = self.clone();
        Box::new(move |event| live.0.borrow_mut().on_session(event))
    }

    pub fn equivalence_started(
        &self,
        file: &str,
        proofstep: usize,
        left: &str,
        right: &str,
        oracles: &[String],
    ) {
        let mut live = self.0.borrow_mut();
        live.eqs.push(EqRec {
            file: file.to_string(),
            proofstep,
            left: left.to_string(),
            right: right.to_string(),
            oracles: oracles
                .iter()
                .map(|name| OracleRec {
                    name: name.clone(),
                    nodes: Vec::new(),
                    roots: Vec::new(),
                    lockstep_href: None,
                    summary: None,
                    started: false,
                })
                .collect(),
            setup_steps: 0,
            base_case_admitted: false,
            report_file: None,
            finished: false,
        });
        live.cur_eq = Some(live.eqs.len() - 1);
        live.cur_oracle = None;
        live.node_stack.clear();
        live.live_steps.clear();
        live.oracle_index = 0;
        live.oracle_total = oracles.len();
        live.progress.on_event(&ExportEvent::PhaseStarted {
            phase: ExportPhase::Tactics,
            total_items: oracles.len(),
        });
        live.touch(true);
    }

    pub fn oracle_started(&self, oracle: &str) {
        let mut live = self.0.borrow_mut();
        let Some(eq) = live.cur_eq else { return };
        let Some(idx) = live.eqs[eq].oracles.iter().position(|o| o.name == oracle) else {
            return;
        };
        live.eqs[eq].oracles[idx].started = true;
        live.cur_oracle = Some(idx);
        live.node_stack.clear();
        live.oracle_index += 1;
        let name = format!("{} {oracle}", live.eqs[eq].file.trim_end_matches(".ec"));
        let index = live.oracle_index;
        live.progress.on_event(&ExportEvent::ItemStarted {
            phase: ExportPhase::Tactics,
            name: &name,
            index,
        });
        live.touch(false);
    }

    /// What the run is doing while no goal is in front (shown in the header).
    pub fn activity(&self, text: &str) {
        let mut live = self.0.borrow_mut();
        live.activity = text.to_string();
        live.touch(true);
    }

    /// Lockstep execution of the current oracle is done; its page is in `out_dir`.
    pub fn lockstep_done(&self, out_dir: &Path) {
        let mut live = self.0.borrow_mut();
        let href = relative_href(&live.page_dir, &out_dir.join("index.html"));
        if let (Some(eq), Some(o)) = (live.cur_eq, live.cur_oracle) {
            live.eqs[eq].oracles[o].lockstep_href = href;
        }
        live.touch(true);
    }

    /// The prover starts on joint node `lockstep_node` (`None` for the router prelude).
    pub fn node_entered(
        &self,
        label: &str,
        kind: &str,
        mut ids: Vec<String>,
        lockstep_node: Option<usize>,
    ) {
        let mut live = self.0.borrow_mut();
        let (Some(eq), Some(o)) = (live.cur_eq, live.cur_oracle) else {
            return;
        };
        let more_ids = ids.len().saturating_sub(IDS_PER_NODE);
        ids.truncate(IDS_PER_NODE);
        let parent = live.node_stack.last().copied();
        let oracle = &mut live.eqs[eq].oracles[o];
        oracle.nodes.push(NodeRec {
            label: label.to_string(),
            kind: kind.to_string(),
            ids,
            more_ids,
            lockstep_node,
            children: Vec::new(),
            steps: Vec::new(),
            rungs: Vec::new(),
            admits: Vec::new(),
            done: false,
        });
        let idx = oracle.nodes.len() - 1;
        match parent {
            Some(p) => oracle.nodes[p].children.push(idx),
            None => oracle.roots.push(idx),
        }
        live.node_stack.push(idx);
        live.touch(false);
    }

    pub fn node_left(&self) {
        let mut live = self.0.borrow_mut();
        let (Some(eq), Some(o)) = (live.cur_eq, live.cur_oracle) else {
            return;
        };
        let Some(idx) = live.node_stack.pop() else {
            return;
        };
        let node = &mut live.eqs[eq].oracles[o].nodes[idx];
        node.done = true;
        let (label, admitted) = (node.label.clone(), !node.admits.is_empty());
        let oracle = live.eqs[eq].oracles[o].name.clone();
        live.progress.on_event(&ExportEvent::GoalFinished {
            oracle: &oracle,
            goal: &label,
            admitted,
        });
        live.touch(false);
    }

    /// The prover is about to try a rung of the ladder (`rung 0`, `smt()`, …).
    pub fn rung(&self, name: &str) {
        let mut live = self.0.borrow_mut();
        if let Some(node) = live.current_node_mut() {
            if node.rungs.last().map(String::as_str) != Some(name) {
                node.rungs.push(name.to_string());
            }
        }
    }

    pub fn admitted(&self, admit: &Admit) {
        let mut live = self.0.borrow_mut();
        let rec = AdmitRec {
            label: admit.label(),
            id: admit.id.clone(),
            reason: admit.reason.slug(),
        };
        if let Some(node) = live.current_node_mut() {
            node.admits.push(rec);
        }
        live.touch(false);
    }

    pub fn oracle_finished(&self, result: &OracleTactics) {
        let mut live = self.0.borrow_mut();
        let Some(eq) = live.cur_eq else { return };
        let Some(idx) = live.eqs[eq]
            .oracles
            .iter()
            .position(|o| o.name == result.oracle)
        else {
            return;
        };
        if live.eqs[eq].oracles[idx].summary.is_some() {
            return;
        }
        live.eqs[eq].oracles[idx].summary = Some(OracleSummary {
            closed: result.stats.closed,
            fallbacks: result.stats.fallbacks,
            undone: result.stats.attempts_undone,
            admits: result
                .admits_by_reason()
                .into_iter()
                .map(|(r, n)| (r.slug(), n))
                .collect(),
            admit_total: result.stats.admits.len(),
            ec_ms: result.easycrypt_time.as_millis() as u64,
            problem: result.problem.clone(),
            alignment_mismatches: result.alignment_mismatches.len(),
            joint_paths: result.joint_paths,
            nodes: result.nodes,
            stuck_points: result.stuck_points,
        });
        if live.cur_oracle == Some(idx) {
            live.cur_oracle = None;
            live.node_stack.clear();
        }
        live.touch(true);
    }

    pub fn equivalence_finished(&self, result: &EquivalenceTactics) {
        let mut live = self.0.borrow_mut();
        let Some(eq) = live.cur_eq else { return };
        live.eqs[eq].base_case_admitted = result.base_case_admitted;
        live.eqs[eq].report_file = Some(result.report_file.clone());
        live.eqs[eq].finished = true;
        live.cur_oracle = None;
        live.node_stack.clear();
        live.progress.on_event(&ExportEvent::PhaseFinished {
            phase: ExportPhase::Tactics,
        });
        live.touch(true);
    }

    /// The last write: no refresh tag, the summary of the whole theorem.
    pub fn finish(&self) {
        let mut live = self.0.borrow_mut();
        live.state = RunState::Done;
        live.pending = None;
        live.cur_eq = None;
        live.cur_oracle = None;
        live.node_stack.clear();
        live.touch(true);
    }

    /// The run ended in an error: the page stays as it is, without the refresh tag, and says so.
    pub fn fail(&self, message: &str) {
        let mut live = self.0.borrow_mut();
        live.state = RunState::Failed(message.to_string());
        live.pending = None;
        live.touch(true);
    }

    /// The run was stopped by Ctrl-C (story 34): nothing went wrong, so not [`Self::fail`]. The
    /// page stays as it is, without the refresh tag, and says what was sealed (`sealed`, as the
    /// report says it).
    pub fn interrupted(&self, sealed: &str) {
        let mut live = self.0.borrow_mut();
        live.state = RunState::Interrupted(sealed.to_string());
        live.pending = None;
        live.touch(true);
    }
}

impl Live {
    fn current_node_mut(&mut self) -> Option<&mut NodeRec> {
        let (eq, o) = (self.cur_eq?, self.cur_oracle?);
        let idx = *self.node_stack.last()?;
        self.eqs.get_mut(eq)?.oracles.get_mut(o)?.nodes.get_mut(idx)
    }

    fn on_session(&mut self, event: &SessionEvent<'_>) {
        match event {
            SessionEvent::Sending { sentence } => {
                self.pending = Some(Pending {
                    sentence: (*sentence).to_string(),
                    since: Instant::now(),
                    before: self.last_answered,
                });
                self.touch(false);
            }
            SessionEvent::Waiting { .. } => self.touch(false),
            SessionEvent::Answered {
                sentence,
                response,
                elapsed,
                record_bytes,
                stopped,
            } => {
                self.pending = None;
                let record = record_bytes.map(|len| RecordSpan {
                    line: self.lines,
                    offset: self.offset,
                    len,
                });
                if let Some(span) = record {
                    self.lines += 1;
                    self.offset += span.len as u64;
                }
                let undo_to = parse_undo(sentence);
                let step = Step {
                    record,
                    sentence: (*sentence).to_string(),
                    status: match response.status {
                        Status::Ok => StepStatus::Accepted,
                        Status::Error => StepStatus::Failed,
                        Status::Interrupted if *stopped => StepStatus::Interrupted,
                        Status::Interrupted => StepStatus::TimedOut,
                    },
                    undone: false,
                    is_undo: undo_to.is_some(),
                    error: response.error.as_ref().map(|e| cap(&e.msg, MESSAGE_CAP)),
                    messages: response
                        .messages
                        .iter()
                        .take(5)
                        .map(|m| cap(&format!("{}: {}", m.level, m.text), MESSAGE_CAP))
                        .collect(),
                    ms: elapsed.as_millis() as u64,
                    state: response.state,
                    goals_left: response.proof.as_ref().map_or(0, |p| p.goals.len()),
                };
                let id = self.steps.len();
                if let Some(to) = undo_to {
                    // the sentences accepted after depth `to` are gone
                    while let Some(&top) = self.live_steps.last() {
                        if self.steps[top].state <= to {
                            break;
                        }
                        self.steps[top].undone = true;
                        self.live_steps.pop();
                    }
                } else if step.status == StepStatus::Accepted {
                    self.live_steps.push(id);
                }
                let is_undo = step.is_undo;
                self.steps.push(step);
                self.last_answered = Some(id);
                if !is_undo {
                    self.attach(id);
                }
                self.touch(false);
            }
            // the session warned on stderr; the steps from here on have no record
            SessionEvent::TranscriptDropped { .. } => {}
        }
    }

    /// Puts a step in the goal being worked on, or counts it as set-up.
    fn attach(&mut self, id: usize) {
        if let Some(node) = self.current_node_mut() {
            node.steps.push(id);
        } else if let Some(eq) = self.cur_eq {
            self.eqs[eq].setup_steps += 1;
        }
    }

    /// Rewrites the page: unless throttled, or `force`.
    fn touch(&mut self, force: bool) {
        let Some(path) = self.page.clone() else {
            return;
        };
        if !force
            && self
                .last_flush
                .is_some_and(|at| at.elapsed() < self.flush_gap)
        {
            return;
        }
        self.last_flush = Some(Instant::now());
        let html = self.render_html();
        let _ = write_atomically(&path, &html);
    }

    /// The steps whose goal text is embedded now.
    pub(super) fn shown_steps(&self, running: bool) -> BTreeSet<usize> {
        let mut shown = BTreeSet::new();
        for eq in &self.eqs {
            for oracle in &eq.oracles {
                for node in &oracle.nodes {
                    if let Some(&last) = node.steps.last() {
                        shown.insert(last);
                    }
                }
            }
        }
        if running {
            if let Some(pending) = &self.pending {
                shown.extend(pending.before);
            }
            if let (Some(eq), Some(o), Some(&n)) =
                (self.cur_eq, self.cur_oracle, self.node_stack.last())
            {
                let steps = &self.eqs[eq].oracles[o].nodes[n].steps;
                shown.extend(steps.iter().rev().take(CURRENT_STEPS_SHOWN));
            }
        }
        shown
    }

    /// Reads the goal text of every step in `shown` that has a record and no text yet from the
    /// transcript.
    pub(super) fn load_texts(&mut self, shown: &BTreeSet<usize>) {
        let spans: Vec<(usize, u64, usize)> = shown
            .iter()
            .filter(|id| !self.texts.contains_key(id))
            .filter_map(|&id| self.steps[id].record.map(|r| (id, r.offset, r.len)))
            .collect();
        if spans.is_empty() {
            return;
        }
        let wanted: Vec<usize> = spans.iter().map(|&(id, _, _)| id).collect();
        let path = self.transcript.clone();
        // parsing is recursive and the goals nest deeply: the session's reader has the same stack
        let read = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || {
                spans
                    .into_iter()
                    .map(|(id, offset, len)| (id, read_goal_texts(&path, offset, len)))
                    .collect::<Vec<_>>()
            })
            .ok()
            .and_then(|h| h.join().ok());
        match read {
            Some(read) => self.texts.extend(read),
            None => {
                for id in wanted {
                    self.texts.insert(
                        id,
                        GoalTexts {
                            unreadable: true,
                            ..GoalTexts::default()
                        },
                    );
                }
            }
        }
    }

    pub(super) fn text_of(&self, id: usize) -> Option<&GoalTexts> {
        self.texts.get(&id)
    }
}

fn parse_undo(sentence: &str) -> Option<u64> {
    sentence
        .trim()
        .strip_prefix("undo ")?
        .trim_end_matches('.')
        .trim()
        .parse()
        .ok()
}

fn cap(text: &str, max: usize) -> String {
    if text.chars().count() <= max {
        return text.to_string();
    }
    let mut cut: String = text.chars().take(max).collect();
    cut.push_str(" [...]");
    cut
}

/// Writes next to the page and renames, so a browser never reads half a page.
fn write_atomically(path: &Path, text: &str) -> std::io::Result<()> {
    let tmp = path.with_extension("html.tmp");
    std::fs::write(&tmp, text)?;
    std::fs::rename(&tmp, path)
}

/// `to`, as a link relative to the directory `from` (both existing).
pub(super) fn relative_href(from: &Path, to: &Path) -> Option<String> {
    let from = std::fs::canonicalize(from).ok()?;
    let to_dir = std::fs::canonicalize(to.parent()?).ok()?;
    let file = to.file_name()?.to_string_lossy().to_string();
    let a: Vec<_> = from.components().collect();
    let b: Vec<_> = to_dir.components().collect();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut parts: Vec<String> = vec!["..".to_string(); a.len() - common];
    parts.extend(
        b[common..]
            .iter()
            .map(|c| c.as_os_str().to_string_lossy().to_string()),
    );
    parts.push(file);
    Some(parts.join("/"))
}

#[derive(Deserialize)]
struct RecordT {
    response: ResponseT,
}
#[derive(Deserialize)]
struct ResponseT {
    #[serde(default)]
    proof: Option<ProofT>,
}
/// A full answer's proof, or a capped one's (`goals_dropped`, `text_dropped`: story 31).
#[derive(Deserialize)]
struct ProofT {
    goals: Vec<GoalT>,
    #[serde(default)]
    goals_dropped: usize,
}
#[derive(Deserialize)]
struct GoalT {
    #[serde(default)]
    text: String,
    #[serde(default)]
    text_dropped: usize,
}

/// The `pp` of the goals in the transcript record at `offset`, cut to the embedding limits. A
/// capped record is cut to them already, and says how much more the answer held.
fn read_goal_texts(path: &Path, offset: u64, len: usize) -> GoalTexts {
    use std::io::{Read, Seek, SeekFrom};
    let read = || -> std::io::Result<Vec<u8>> {
        let mut file = std::fs::File::open(path)?;
        file.seek(SeekFrom::Start(offset))?;
        let mut buf = vec![0; len];
        file.read_exact(&mut buf)?;
        Ok(buf)
    };
    let parsed = read().ok().and_then(|buf| {
        let mut de = serde_json::Deserializer::from_slice(&buf);
        de.disable_recursion_limit();
        let record = serde::Deserialize::deserialize(&mut de).ok()?;
        Some::<RecordT>(record)
    });
    let Some(record) = parsed else {
        return GoalTexts {
            unreadable: true,
            ..GoalTexts::default()
        };
    };
    let (goals, goals_dropped) = record
        .response
        .proof
        .map_or((Vec::new(), 0), |p| (p.goals, p.goals_dropped));
    let mut texts = GoalTexts {
        total: goals.len() + goals_dropped,
        ..GoalTexts::default()
    };
    for goal in goals.into_iter().take(GOALS_PER_STEP) {
        let chars = goal.text.chars().count();
        texts
            .cut
            .push(chars.saturating_sub(GOAL_TEXT_CAP) + goal.text_dropped);
        texts
            .goals
            .push(goal.text.chars().take(GOAL_TEXT_CAP).collect());
    }
    texts
}

/// The page without its timings element: what two runs of an unchanged project have in common.
pub fn strip_timings(html: &str) -> String {
    let open = "<script id=\"timings\"";
    let Some(start) = html.find(open) else {
        return html.to_string();
    };
    let Some(end) = html[start..].find("</script>") else {
        return html.to_string();
    };
    format!(
        "{}{}",
        &html[..start],
        &html[start + end + "</script>".len()..]
    )
}

#[cfg(test)]
mod tests;
