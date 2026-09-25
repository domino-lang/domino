// SPDX-License-Identifier: MIT OR Apache-2.0

//! A live `easycrypt cli -json` process (story 26 §3.1).
//!
//! [`Session::send`] writes one sentence and reads the one JSON line EasyCrypt answers with
//! (`easycrypt/doc/json-output.md`). The state of the session after the sentence is the
//! returned [`Response`]; [`Session::undo_to`] goes back to an earlier one in O(1). Every
//! exchange is kept in [`Session::transcript`]; with a transcript sink it is also written to
//! `ec-transcript.jsonl` as it happens ([`Session::set_transcript_sink`], module [`transcript`]).
//!
//! The binary is found through the `DOMINO_EASYCRYPT` environment variable, falling back to
//! `easycrypt` on `PATH`, and is checked at startup: a binary that does not answer in
//! `domino-json/1` is refused with a message naming the variable and the branch of the
//! EasyCrypt clone that adds the format.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::sync::Arc;
use std::time::{Duration, Instant};

use thiserror::Error;

use super::json::{self, Goal, Response, Status, FORMAT_VERSION};
use super::transcript::{self, EcTranscriptMode};

/// The environment variable naming the `-json`-capable EasyCrypt binary.
pub const ENV_VAR: &str = "DOMINO_EASYCRYPT";

/// The EasyCrypt clone branch that adds `cli -json` (story 25).
const JSON_BRANCH: &str = "amir/domino-easycrypt-integration";

/// How long a sentence may run before it is interrupted, unless [`Session::set_timeout`] says
/// otherwise.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(600);

/// How long the answer to a `SIGINT` may take.
const INTERRUPT_GRACE: Duration = Duration::from_secs(30);

/// How long reading the goals again may take ([`Session::send`] on an answer that lost them).
const REREAD_TIMEOUT: Duration = Duration::from_secs(120);

/// How often a running sentence looks at the stop flag ([`Session::set_stop`]).
const STOP_POLL: Duration = Duration::from_millis(100);

/// The startup check's sentence: it changes no state and is answered with one line.
const PROBE_SENTENCE: &str = "pragma Goals:printall.";

#[derive(Debug, Error)]
pub enum SessionError {
    #[error("could not start EasyCrypt (`{}`): {source}. Set {ENV_VAR} to an EasyCrypt binary that supports `cli -json` (branch {JSON_BRANCH} of the EasyCrypt clone; a binary built there is only found by its theories when invoked as `ec.native`)", binary.display())]
    Spawn {
        binary: PathBuf,
        source: std::io::Error,
    },
    #[error("`{}` does not speak `{FORMAT_VERSION}` ({detail}). Set {ENV_VAR} to an EasyCrypt binary built from branch {JSON_BRANCH} of the EasyCrypt clone", binary.display())]
    NotJsonCapable { binary: PathBuf, detail: String },
    #[error("EasyCrypt closed its output while answering `{sentence}`")]
    Closed { sentence: String },
    #[error("EasyCrypt answered `{sentence}` with something that is not `{FORMAT_VERSION}`: {source}")]
    BadAnswer {
        sentence: String,
        source: serde_json::Error,
    },
    #[error("EasyCrypt refused `{sentence}`, which the prover relies on: {msg}")]
    Refused { sentence: String, msg: String },
    #[error("EasyCrypt did not answer `{sentence}` after being interrupted")]
    Unresponsive { sentence: String },
    #[error("EasyCrypt could not print the goals after `{sentence}`")]
    GoalsLost { sentence: String },
    /// The run was asked to stop (Ctrl-C, story 34). Not EasyCrypt's doing: the prover returns
    /// it to unwind, once it has sealed what it proved.
    #[error("the run was stopped (Ctrl-C)")]
    Stopped,
    #[error("could not write the EasyCrypt transcript `{}` (`--ec-transcript full`): {source}", path.display())]
    Transcript {
        path: PathBuf,
        source: std::io::Error,
    },
    #[error("io error talking to EasyCrypt: {0}")]
    Io(#[from] std::io::Error),
}

/// One sentence and EasyCrypt's answer to it.
#[derive(Debug, Clone)]
pub struct Exchange {
    pub sentence: String,
    pub response: Response,
}

/// A line of EasyCrypt's output and its parse, done on the reader thread (see
/// [`READER_STACK`]).
struct Line {
    raw: String,
    parsed: Result<Response, serde_json::Error>,
}

/// The stack of the thread that reads and parses EasyCrypt's answers: a goal's formulas nest
/// deeply, and parsing is recursive.
const READER_STACK: usize = 1 << 30;

/// What [`Session::send`] tells its observer (story 28): the sentence about to run, a tick while
/// it is still running, and its answer.
#[derive(Debug)]
pub enum SessionEvent<'a> {
    Sending { sentence: &'a str },
    /// EasyCrypt has not answered yet; sent every [`WAIT_TICK`].
    Waiting { sentence: &'a str, elapsed: Duration },
    /// The answer. `record_bytes` is the size of the transcript record just written, if there
    /// is a transcript sink (the record is on disk already). `stopped`: the sentence was
    /// interrupted because the run was asked to stop ([`Session::set_stop`]), not by the timeout.
    Answered {
        sentence: &'a str,
        response: &'a Response,
        elapsed: Duration,
        record_bytes: Option<usize>,
        stopped: bool,
    },
    /// Writing the transcript failed under [`EcTranscriptMode::Capped`]: no record is written
    /// from this sentence on (story 31 §3.3). Sent once, before that sentence's `Answered`.
    TranscriptDropped { path: &'a Path, cause: &'a str },
}

/// How often a running sentence is reported to the observer as [`SessionEvent::Waiting`].
pub const WAIT_TICK: Duration = Duration::from_secs(1);

pub struct Session {
    child: Child,
    stdin: Option<ChildStdin>,
    lines: Receiver<std::io::Result<Line>>,
    binary: PathBuf,
    transcript: Vec<Exchange>,
    /// The state before the first sentence: no proof, depth 0.
    empty: Option<Response>,
    timeout: Duration,
    sink: Option<TranscriptSink>,
    /// A capped transcript's write failed and the sink was dropped.
    sink_dropped: bool,
    observer: Option<Box<dyn FnMut(&SessionEvent<'_>)>>,
    /// Set when the run is asked to stop (Ctrl-C): see [`Session::set_stop`].
    stop: Option<Arc<AtomicBool>>,
}

/// How waiting for an answer ended.
enum Wait {
    Line(std::io::Result<Line>),
    TimedOut,
    /// The stop flag was set while the sentence ran.
    Stopped,
    Closed,
}

/// Where [`Session::send`] appends every exchange, one record per line
/// ([`transcript::record`]): `{"file": <tag>, "ctx": <the caller's note>, "sentence": <the
/// sentence>, "ms": <how long EasyCrypt took>, "response": <EasyCrypt's answer>}`, the answer
/// capped or verbatim by `mode`.
///
/// Records are only ever appended, each capped as it is written: the live page holds the byte
/// offset of every record it has seen, so the file must never be compacted, compressed or
/// rewritten afterwards (see [`transcript`]).
struct TranscriptSink {
    writer: Box<dyn Write + Send>,
    /// Named in the warning or error when a write fails.
    path: PathBuf,
    mode: EcTranscriptMode,
    tag: String,
    /// What the caller says it is working on; written with every record.
    context: String,
}

/// The binary a session will run: `DOMINO_EASYCRYPT`, else `easycrypt`.
pub fn locate_binary() -> PathBuf {
    match std::env::var_os(ENV_VAR) {
        Some(path) if !path.is_empty() => PathBuf::from(path),
        _ => PathBuf::from("easycrypt"),
    }
}

/// Whether [`ENV_VAR`] names a binary, for tests that need a `-json`-capable EasyCrypt and
/// skip when there is none.
pub fn json_binary_configured() -> bool {
    std::env::var_os(ENV_VAR).is_some_and(|v| !v.is_empty())
}

impl Session {
    /// Starts [`locate_binary`]'s EasyCrypt with `dir` as working directory and `-I dir`.
    pub fn start(dir: &Path) -> Result<Session, SessionError> {
        Session::start_with(&locate_binary(), dir)
    }

    pub fn start_with(binary: &Path, dir: &Path) -> Result<Session, SessionError> {
        let mut child = Command::new(binary)
            .args(["cli", "-json", "-I"])
            .arg(dir)
            .current_dir(dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|source| SessionError::Spawn {
                binary: binary.to_path_buf(),
                source,
            })?;
        let stdin = child.stdin.take();
        let stdout = child.stdout.take().expect("stdout is piped");
        let (tx, lines) = mpsc::channel();
        std::thread::Builder::new()
            .stack_size(READER_STACK)
            .spawn(move || {
                let mut reader = BufReader::new(stdout);
                loop {
                    let mut line = String::new();
                    match reader.read_line(&mut line) {
                        Ok(0) => break,
                        Ok(_) => {
                            let parsed = json::parse_response(&line);
                            if tx.send(Ok(Line { raw: line, parsed })).is_err() {
                                break;
                            }
                        }
                        Err(e) => {
                            let _ = tx.send(Err(e));
                            break;
                        }
                    }
                }
            })?;
        let mut session = Session {
            child,
            stdin,
            lines,
            binary: binary.to_path_buf(),
            transcript: Vec::new(),
            empty: None,
            timeout: DEFAULT_TIMEOUT,
            sink: None,
            sink_dropped: false,
            observer: None,
            stop: None,
        };
        session.check_capability()?;
        Ok(session)
    }

    fn check_capability(&mut self) -> Result<(), SessionError> {
        let binary = self.binary.clone();
        let not_json = |detail: String| SessionError::NotJsonCapable {
            binary: binary.clone(),
            detail,
        };
        self.write_line(PROBE_SENTENCE)?;
        let line = match self.lines.recv_timeout(Duration::from_secs(120)) {
            Ok(Ok(line)) => line,
            Ok(Err(e)) => return Err(not_json(e.to_string())),
            Err(RecvTimeoutError::Timeout) => return Err(not_json("no answer".into())),
            Err(RecvTimeoutError::Disconnected) => {
                return Err(not_json("it exited without answering".into()))
            }
        };
        let response = line.parsed.map_err(|e| not_json(e.to_string()))?;
        if response.version != FORMAT_VERSION {
            return Err(not_json(format!("version `{}`", response.version)));
        }
        self.empty = Some(Response {
            state: 0,
            proof: None,
            error: None,
            messages: Vec::new(),
            status: Status::Ok,
            ..response
        });
        Ok(())
    }

    /// How long a sentence may run before it is interrupted (and answered `interrupted`).
    pub fn set_timeout(&mut self, timeout: Duration) {
        self.timeout = timeout;
    }

    /// Appends every later exchange to `writer` as one JSON line (`{"file": tag, "ctx": …,
    /// "sentence": …, "ms": …, "response": …}`), undone attempts included. This is
    /// `ec-transcript.jsonl` at `path` (story 27 §3.7); `mode` says whether EasyCrypt's answers
    /// are written verbatim or with their goals capped (story 31, [`transcript`]).
    ///
    /// A failed write fails [`Session::send`] under [`EcTranscriptMode::Full`]. Under
    /// [`EcTranscriptMode::Capped`] it drops the sink instead, with a warning on stderr and a
    /// [`SessionEvent::TranscriptDropped`]: a transcript is not worth a proof.
    pub fn set_transcript_sink(
        &mut self,
        writer: Box<dyn Write + Send>,
        path: &Path,
        mode: EcTranscriptMode,
        tag: &str,
    ) {
        self.sink = Some(TranscriptSink {
            writer,
            path: path.to_path_buf(),
            mode,
            tag: tag.to_string(),
            context: String::new(),
        });
    }

    /// Whether a capped transcript's write failed and the sink was dropped: a later session of
    /// the same run should not write to the same file (its records would have no known offset).
    pub fn transcript_dropped(&self) -> bool {
        self.sink_dropped
    }

    /// Calls `observer` before every later sentence, every [`WAIT_TICK`] while it runs, and with
    /// its answer (the live translation page, story 28). It sees nothing it could change.
    pub fn set_observer(&mut self, observer: Box<dyn FnMut(&SessionEvent<'_>)>) {
        self.observer = Some(observer);
    }

    fn notify(&mut self, event: &SessionEvent<'_>) {
        if let Some(observer) = &mut self.observer {
            observer(event);
        }
    }

    /// `stop` is the run's stop flag (story 34), set by a Ctrl-C handler. A sentence running
    /// when it is set is interrupted at once, as the timeout would, and its answer reported with
    /// `stopped` ([`SessionEvent::Answered`]). The session sends nothing on its own: what comes
    /// next is the caller's decision ([`Session::stop_requested`]). Sentences sent once the flag
    /// is set, and `undo`s, run to their end. If the interrupted sentence's answer lost its
    /// goals ([`Response::goals_lost`]), they are not read again: the caller is stopping, and
    /// knows the goals from before the sentence.
    pub fn set_stop(&mut self, stop: Arc<AtomicBool>) {
        self.stop = Some(stop);
    }

    /// Whether the run has been asked to stop ([`Session::set_stop`]).
    pub fn stop_requested(&self) -> bool {
        self.stop.as_ref().is_some_and(|s| s.load(Ordering::Relaxed))
    }

    /// Waits for the next line, up to the timeout, reporting [`SessionEvent::Waiting`] on the
    /// way; `stoppable`: also until the stop flag is set.
    fn wait_line(&mut self, sentence: &str, began: Instant, stoppable: bool) -> Wait {
        let deadline = began + self.timeout;
        let mut next_tick = began + WAIT_TICK;
        loop {
            if stoppable && self.stop_requested() {
                return Wait::Stopped;
            }
            let now = Instant::now();
            if now >= deadline {
                return Wait::TimedOut;
            }
            let mut until = deadline;
            if self.observer.is_some() {
                until = until.min(next_tick);
            }
            if stoppable {
                until = until.min(now + STOP_POLL);
            }
            match self.lines.recv_timeout(until.saturating_duration_since(now)) {
                Ok(line) => return Wait::Line(line),
                Err(RecvTimeoutError::Disconnected) => return Wait::Closed,
                Err(RecvTimeoutError::Timeout) => {
                    if self.observer.is_some() && Instant::now() >= next_tick {
                        self.notify(&SessionEvent::Waiting {
                            sentence,
                            elapsed: began.elapsed(),
                        });
                        next_tick += WAIT_TICK;
                    }
                }
            }
        }
    }

    /// A free-form note (the oracle and joint node being worked on) that goes into every later
    /// transcript record as `"ctx"`. Without a transcript sink it is ignored.
    pub fn set_context(&mut self, context: &str) {
        if let Some(sink) = &mut self.sink {
            sink.context = context.to_string();
        }
    }

    /// The current per-sentence timeout.
    pub fn timeout(&self) -> Duration {
        self.timeout
    }

    /// The binary this session runs.
    pub fn binary(&self) -> &Path {
        &self.binary
    }

    fn write_line(&mut self, sentence: &str) -> Result<(), SessionError> {
        let stdin = self.stdin.as_mut().ok_or_else(|| SessionError::Closed {
            sentence: sentence.to_string(),
        })?;
        // A sentence is one line for EasyCrypt: its own line breaks are whitespace.
        let flat = sentence.replace('\n', " ");
        stdin.write_all(flat.as_bytes())?;
        stdin.write_all(b"\n")?;
        stdin.flush()?;
        Ok(())
    }

    /// Sends one sentence and returns EasyCrypt's answer. A sentence still running after the
    /// timeout, or when the run is asked to stop ([`Session::set_stop`]), is interrupted, and
    /// the answer is then `Status::Interrupted`.
    pub fn send(&mut self, sentence: &str) -> Result<&Response, SessionError> {
        self.exchange(sentence, true)
    }

    /// [`Session::send`]; `stoppable`: a stop request interrupts the sentence.
    fn exchange(&mut self, sentence: &str, stoppable: bool) -> Result<&Response, SessionError> {
        let began = Instant::now();
        // a stop known before the sentence was sent is the caller's to act on
        let stoppable = stoppable && !self.stop_requested();
        self.notify(&SessionEvent::Sending { sentence });
        self.write_line(sentence)?;
        let (line, timed_out) = match self.wait_line(sentence, began, stoppable) {
            Wait::Line(line) => (line, false),
            Wait::TimedOut | Wait::Stopped => {
                let timed_out = !self.stop_requested();
                self.interrupt()?;
                let line = self.lines.recv_timeout(INTERRUPT_GRACE).map_err(|_| {
                    SessionError::Unresponsive {
                        sentence: sentence.to_string(),
                    }
                })?;
                (line, timed_out)
            }
            Wait::Closed => {
                return Err(SessionError::Closed {
                    sentence: sentence.to_string(),
                })
            }
        };
        let line = line?;
        let record_bytes = self.write_record(sentence, began.elapsed(), &line.raw)?;
        let mut response = line.parsed.map_err(|source| SessionError::BadAnswer {
            sentence: sentence.to_string(),
            source,
        })?;
        // an interrupt that landed while EasyCrypt printed the goals: read them again, unless
        // this is the sentence a stop interrupted (the caller stops, and knows the goals from
        // before it; reading them costs as much as printing them did)
        if response.goals_lost() && !(stoppable && self.stop_requested()) {
            response.proof = self.reread_goals(sentence)?;
        }
        // A goal is hundreds of kilobytes of JSON: only the newest answer keeps its goals.
        if let Some(previous) = self.transcript.last_mut() {
            previous.response.proof = None;
        }
        // a Ctrl-C reaches EasyCrypt itself too, so its answer can come before the flag is seen
        let stopped = response.status == Status::Interrupted && !timed_out && self.stop_requested();
        self.transcript.push(Exchange {
            sentence: sentence.to_string(),
            response,
        });
        if self.observer.is_some() {
            let exchange = self.transcript.last().expect("just pushed");
            let event = SessionEvent::Answered {
                sentence,
                response: &exchange.response,
                elapsed: began.elapsed(),
                record_bytes,
                stopped,
            };
            // `notify` borrows `self` mutably: take the observer out for the call
            if let Some(mut observer) = self.observer.take() {
                observer(&event);
                self.observer = Some(observer);
            }
        }
        Ok(&self.transcript.last().expect("just pushed").response)
    }

    /// The goals as they are now, read with [`PROBE_SENTENCE`] (which changes no state), for an
    /// answer that lost them ([`Response::goals_lost`]). Not an exchange: the transcript keeps the answer
    /// as EasyCrypt gave it.
    fn reread_goals(&mut self, sentence: &str) -> Result<Option<json::Proof>, SessionError> {
        let lost = || SessionError::GoalsLost {
            sentence: sentence.to_string(),
        };
        self.write_line(PROBE_SENTENCE)?;
        let line = self
            .lines
            .recv_timeout(REREAD_TIMEOUT)
            .map_err(|_| lost())??;
        let response = line.parsed.map_err(|_| lost())?;
        if response.goals_lost() {
            return Err(lost());
        }
        Ok(response.proof)
    }

    /// Appends the record of one exchange to the transcript sink, if any, and returns its size.
    fn write_record(
        &mut self,
        sentence: &str,
        elapsed: Duration,
        answer: &str,
    ) -> Result<Option<usize>, SessionError> {
        let Some(sink) = &mut self.sink else {
            return Ok(None);
        };
        let record = transcript::record(
            sink.mode,
            &sink.tag,
            &sink.context,
            sentence,
            elapsed.as_millis(),
            answer,
        );
        let Err(source) = sink.writer.write_all(record.as_bytes()) else {
            return Ok(Some(record.len()));
        };
        let sink = self.sink.take().expect("matched above");
        if sink.mode == EcTranscriptMode::Full {
            return Err(SessionError::Transcript {
                path: sink.path,
                source,
            });
        }
        self.sink_dropped = true;
        let cause = source.to_string();
        eprintln!(
            "warning: could not write the EasyCrypt transcript `{}`: {cause}. The run goes on \
             without it; the live page shows no goal text from here on.",
            sink.path.display()
        );
        self.notify(&SessionEvent::TranscriptDropped {
            path: &sink.path,
            cause: &cause,
        });
        Ok(None)
    }

    /// Returns to the state whose answer said `state` (`undo <state>.`). A stop request does
    /// not interrupt it: rolling back is how a caller gets to a consistent state to stop in.
    pub fn undo_to(&mut self, state: u64) -> Result<&Response, SessionError> {
        self.exchange(&format!("undo {state}."), false)
    }

    /// Sends `SIGINT` to the process: the running sentence is answered `interrupted` and the
    /// session goes on. One that arrives while EasyCrypt is idle is not answered at all.
    pub fn interrupt(&self) -> std::io::Result<()> {
        Command::new("kill")
            .arg("-INT")
            .arg(self.child.id().to_string())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|_| ())
    }

    /// The answer to the last sentence, or the empty state before any.
    pub fn last(&self) -> Option<&Response> {
        self.transcript
            .last()
            .map(|e| &e.response)
            .or(self.empty.as_ref())
    }

    /// The open goals after the last sentence.
    pub fn goals(&self) -> &[Goal] {
        self.last()
            .and_then(|r| r.proof.as_ref())
            .map_or(&[], |p| p.goals.as_slice())
    }

    /// Every sentence sent since the start, with its answer, in order (an `undo` included). Only
    /// the last answer still carries its goals (`proof`); earlier ones keep status, state, error
    /// and messages, which is what a transcript file needs.
    pub fn transcript(&self) -> &[Exchange] {
        &self.transcript
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        // Closing stdin is an implicit `exit.`; do not wait on a process stuck in a prover.
        self.stdin.take();
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Splits EasyCrypt source into sentences: each ends at a `.` followed by whitespace or the end
/// of the text, outside comments (`(* … *)`, nested) and string literals. Comments are dropped;
/// a sentence's own whitespace is kept.
pub fn split_sentences(source: &str) -> Vec<String> {
    let chars: Vec<char> = source.chars().collect();
    let mut sentences = Vec::new();
    let mut current = String::new();
    let mut depth = 0usize;
    let mut in_string = false;
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if depth > 0 {
            if c == '(' && next == Some('*') {
                depth += 1;
                i += 2;
            } else if c == '*' && next == Some(')') {
                depth -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        if in_string {
            current.push(c);
            if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match c {
            '(' if next == Some('*') => {
                depth = 1;
                i += 2;
                // `(*)` is a section of the operator `( * )` in EasyCrypt; not handled.
            }
            '"' => {
                in_string = true;
                current.push(c);
                i += 1;
            }
            '.' if next.is_none_or(|n| n.is_whitespace()) => {
                current.push(c);
                let sentence = current.trim().to_string();
                if !sentence.is_empty() {
                    sentences.push(sentence);
                }
                current.clear();
                i += 1;
            }
            _ => {
                current.push(c);
                i += 1;
            }
        }
    }
    let rest = current.trim();
    if !rest.is_empty() {
        sentences.push(rest.to_string());
    }
    sentences
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn sentences_end_at_a_dot_before_whitespace() {
        let src = "require import A B.\n(* a (* nested *) comment. *)\nlemma l : Pr[M.f() @ &m : res] = x.\nproof.\nbyequiv\n  (: ={glob A}\n     ==> _) => //.\ncall (: inv {| a = M.x{1} |}); last first.\n";
        let s = split_sentences(src);
        assert_eq!(
            s,
            vec![
                "require import A B.",
                "lemma l : Pr[M.f() @ &m : res] = x.",
                "proof.",
                "byequiv\n  (: ={glob A}\n     ==> _) => //.",
                "call (: inv {| a = M.x{1} |}); last first.",
            ]
        );
    }

    #[test]
    fn a_dot_inside_a_string_or_a_tuple_projection_does_not_end_a_sentence() {
        let s = split_sentences("have := x.`1 = \"a. b\".\nauto.");
        assert_eq!(s, vec!["have := x.`1 = \"a. b\".", "auto."]);
    }

    #[test]
    fn a_binary_that_does_not_speak_json_is_refused_naming_the_variable() {
        let dir = tempfile::tempdir().unwrap();
        // `cat` echoes the probe sentence back, which is not a JSON answer
        let err = Session::start_with(Path::new("cat"), dir.path()).err().unwrap();
        assert!(matches!(err, SessionError::NotJsonCapable { .. }), "{err}");
        assert!(err.to_string().contains(ENV_VAR));
        let err = Session::start_with(Path::new("/nonexistent/easycrypt"), dir.path())
            .err()
            .unwrap();
        assert!(matches!(err, SessionError::Spawn { .. }), "{err}");
        assert!(err.to_string().contains(ENV_VAR));
    }

    /// A stand-in EasyCrypt that answers every line `ok` and takes 2.3 s over "slow" ones.
    #[test]
    fn the_observer_sees_the_sentence_ticks_while_it_runs_and_the_answer() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let script = dir.path().join("fake-easycrypt");
        std::fs::write(
            &script,
            "#!/bin/sh\nwhile IFS= read -r line; do\n  case \"$line\" in *slow*) sleep 2.3;; esac\n  echo '{\"version\":\"domino-json/1\",\"state\":1,\"status\":\"ok\",\"messages\":[]}'\ndone\n",
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        let mut session = Session::start_with(&script, dir.path()).unwrap();
        let events = std::rc::Rc::new(std::cell::RefCell::new(Vec::<String>::new()));
        let seen = events.clone();
        session.set_observer(Box::new(move |e| {
            seen.borrow_mut().push(match e {
                SessionEvent::Sending { sentence } => format!("sending {sentence}"),
                SessionEvent::Waiting { sentence, .. } => format!("waiting {sentence}"),
                SessionEvent::Answered { sentence, record_bytes, .. } => {
                    format!("answered {sentence} {}", record_bytes.is_some())
                }
                SessionEvent::TranscriptDropped { .. } => "dropped".to_string(),
            })
        }));
        session.send("quick.").unwrap();
        session.send("slow.").unwrap();
        let events = events.borrow();
        assert_eq!(events[..2], ["sending quick.", "answered quick. false"]);
        assert_eq!(events[2], "sending slow.");
        let waits = events.iter().filter(|e| e.starts_with("waiting slow.")).count();
        assert_eq!(waits, 2, "a tick each second of the 2.3 s: {events:?}");
        assert_eq!(events.last().unwrap(), "answered slow. false");
    }

    /// A stand-in EasyCrypt that answers `ok` at once, except to lines with `slow` in them and
    /// to `undo`s: those run until a `SIGINT` (answered `interrupted`) or for 2 s (answered
    /// `ok`).
    fn interruptible_easycrypt(dir: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let script = dir.join("fake-easycrypt");
        std::fs::write(
            &script,
            r#"#!/bin/sh
int=0
trap 'int=1' INT
ans() { echo "{\"version\":\"domino-json/1\",\"state\":1,\"status\":\"$1\",\"messages\":[]}"; }
while IFS= read -r line; do
  case "$line" in
    *slow*|undo*)
      int=0; n=0
      while [ $int = 0 ] && [ $n -lt 20 ]; do sleep 0.1; n=$((n+1)); done
      if [ $int = 1 ]; then ans interrupted; else ans ok; fi;;
    *) ans ok;;
  esac
done
"#,
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    /// A session of [`interruptible_easycrypt`] with a stop flag, and whether each answer the
    /// observer saw was to a stop.
    fn stoppable_session(
        dir: &Path,
    ) -> (
        Session,
        std::sync::Arc<std::sync::atomic::AtomicBool>,
        std::rc::Rc<std::cell::RefCell<Vec<bool>>>,
    ) {
        let mut session = Session::start_with(&interruptible_easycrypt(dir), dir).unwrap();
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        session.set_stop(stop.clone());
        let stopped = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let seen = stopped.clone();
        session.set_observer(Box::new(move |e| {
            if let SessionEvent::Answered { stopped, .. } = e {
                seen.borrow_mut().push(*stopped);
            }
        }));
        (session, stop, stopped)
    }

    /// Sets `stop` after `after`, from another thread (as the Ctrl-C handler does).
    fn stop_after(stop: &std::sync::Arc<std::sync::atomic::AtomicBool>, after: Duration) {
        let stop = stop.clone();
        std::thread::spawn(move || {
            std::thread::sleep(after);
            stop.store(true, std::sync::atomic::Ordering::Relaxed);
        });
    }

    #[test]
    fn a_stop_request_interrupts_the_running_sentence_at_once() {
        let dir = tempfile::tempdir().unwrap();
        let (mut session, stop, stopped) = stoppable_session(dir.path());
        assert!(!session.stop_requested());
        stop_after(&stop, Duration::from_millis(300));
        let began = std::time::Instant::now();
        let status = session.send("slow.").unwrap().status;
        assert_eq!(status, Status::Interrupted);
        assert!(began.elapsed() < Duration::from_millis(1500), "{:?}", began.elapsed());
        assert!(session.stop_requested());
        assert_eq!(*stopped.borrow(), [true], "the answer is to the stop");
    }

    #[test]
    fn the_timeout_still_interrupts_and_is_not_a_stop() {
        let dir = tempfile::tempdir().unwrap();
        let (mut session, _stop, stopped) = stoppable_session(dir.path());
        session.set_timeout(Duration::from_millis(300));
        assert_eq!(session.send("slow.").unwrap().status, Status::Interrupted);
        assert_eq!(*stopped.borrow(), [false]);
    }

    #[test]
    fn neither_an_undo_nor_a_sentence_sent_after_the_stop_is_interrupted() {
        let dir = tempfile::tempdir().unwrap();
        let (mut session, stop, stopped) = stoppable_session(dir.path());
        // the stop comes while the undo runs: rolling back is how the prover gets consistent
        stop_after(&stop, Duration::from_millis(300));
        assert_eq!(session.undo_to(1).unwrap().status, Status::Ok);
        // a sentence sent once the stop is known runs to its end
        assert_eq!(session.send("slow.").unwrap().status, Status::Ok);
        assert_eq!(*stopped.borrow(), [false, false]);
    }

    /// An interrupt that lands while EasyCrypt prints the goals leaves an `ok` answer without
    /// them (`cannot serialize the goals: Sys.Break`); a Ctrl-C at a terminal reaches
    /// EasyCrypt itself too, so this happens (story 34, seen on kem-dem).
    #[test]
    fn goals_lost_to_an_interrupt_are_read_again() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let script = dir.path().join("fake-easycrypt");
        std::fs::write(
            &script,
            r#"#!/bin/sh
goal='{"id":1,"concl":{"kind":"app","pp":"c"},"text":"g"}'
while IFS= read -r line; do
  case "$line" in
    pragma*) echo "{\"version\":\"domino-json/1\",\"state\":2,\"status\":\"ok\",\"messages\":[],\"proof\":{\"goals\":[$goal,$goal]}}";;
    *) echo '{"version":"domino-json/1","state":2,"status":"ok","messages":[{"level":"critical","text":"cannot serialize the goals: Sys.Break"}],"proof":null}';;
  esac
done
"#,
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        let mut session = Session::start_with(&script, dir.path()).unwrap();
        let r = session.send("rewrite /inv in hpre.").unwrap();
        assert_eq!((r.status, r.state), (Status::Ok, 2));
        assert_eq!(session.goals().len(), 2);
        assert_eq!(session.transcript().len(), 1, "the re-read is not an exchange");
    }

    /// A stand-in EasyCrypt that answers every line with the contents of `answer`.
    pub(crate) fn fake_easycrypt(dir: &Path, answer: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let answer_file = dir.join("answer.json");
        std::fs::write(&answer_file, format!("{}\n", answer.trim_end())).unwrap();
        let script = dir.join("fake-easycrypt");
        std::fs::write(
            &script,
            format!(
                "#!/bin/sh\nwhile IFS= read -r line; do\n  cat '{}'\ndone\n",
                answer_file.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    /// A transcript writer whose bytes the test can read, and that fails from its `fail_at`th
    /// write on (`usize::MAX`: never).
    #[derive(Clone)]
    pub(crate) struct TestSink {
        bytes: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
        writes: std::sync::Arc<std::sync::atomic::AtomicUsize>,
        fail_at: usize,
    }

    impl TestSink {
        pub(crate) fn new(fail_at: usize) -> TestSink {
            TestSink {
                bytes: Default::default(),
                writes: Default::default(),
                fail_at,
            }
        }
        pub(crate) fn text(&self) -> String {
            String::from_utf8(self.bytes.lock().unwrap().clone()).unwrap()
        }
    }

    impl Write for TestSink {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let n = self.writes.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            if n >= self.fail_at {
                return Err(std::io::Error::other("No space left on device"));
            }
            self.bytes.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    fn fake_session(dir: &Path, answer: &str, sink: &TestSink, mode: EcTranscriptMode) -> Session {
        let script = fake_easycrypt(dir, answer);
        let mut session = Session::start_with(&script, dir).unwrap();
        session.set_transcript_sink(
            Box::new(sink.clone()),
            Path::new("/out/progress/ec-transcript.jsonl"),
            mode,
            "Eq.ec",
        );
        session
    }

    #[test]
    fn the_sink_caps_a_large_answer_to_three_goals_of_twelve_thousand_characters() {
        let dir = tempfile::tempdir().unwrap();
        let answer = crate::easycrypt::transcript::tests::answer_with_goals(10, 50_000);
        let sink = TestSink::new(usize::MAX);
        let mut session = fake_session(dir.path(), &answer, &sink, EcTranscriptMode::Capped);
        session.set_context("O N0");
        let response = session.send("auto.").unwrap();
        assert_eq!(response.proof.as_ref().unwrap().goals.len(), 10, "the session sees them all");
        let text = sink.text();
        assert_eq!(text.lines().count(), 1);
        let record: serde_json::Value = serde_json::from_str(&text).unwrap();
        assert_eq!(record["file"], "Eq.ec");
        assert_eq!(record["ctx"], "O N0");
        assert_eq!(record["sentence"], "auto.");
        let (capped, full) = (&record["response"], serde_json::from_str::<serde_json::Value>(&answer).unwrap());
        for key in ["version", "state", "status", "error", "messages"] {
            assert_eq!(capped[key], full[key], "{key}");
        }
        let goals = capped["proof"]["goals"].as_array().unwrap();
        assert_eq!(goals.len(), 3);
        assert_eq!(capped["proof"]["goals_dropped"], 7);
        for goal in goals {
            assert_eq!(goal["text"].as_str().unwrap().chars().count(), 12_000);
            assert_eq!(goal["text_dropped"], 38_000);
        }
    }

    #[test]
    fn the_full_sink_writes_the_answer_verbatim() {
        let dir = tempfile::tempdir().unwrap();
        let answer =
            std::fs::read_to_string("testdata/easycrypt/story31/answer-two-goals.json").unwrap();
        let sink = TestSink::new(usize::MAX);
        let mut session = fake_session(dir.path(), &answer, &sink, EcTranscriptMode::Full);
        session.send("split.").unwrap();
        let text = sink.text();
        let ms: serde_json::Value = serde_json::from_str(&text).unwrap();
        assert_eq!(
            text,
            format!(
                "{{\"file\":\"Eq.ec\",\"ctx\":\"\",\"sentence\":\"split.\",\"ms\":{},\"response\":{}}}\n",
                ms["ms"],
                answer.trim_end()
            )
        );
    }

    #[test]
    fn a_failed_capped_write_drops_the_transcript_once_and_the_session_goes_on() {
        let dir = tempfile::tempdir().unwrap();
        let answer = crate::easycrypt::transcript::tests::answer_with_goals(1, 10);
        let sink = TestSink::new(2);
        let mut session = fake_session(dir.path(), &answer, &sink, EcTranscriptMode::Capped);
        let events = std::rc::Rc::new(std::cell::RefCell::new(Vec::<String>::new()));
        let seen = events.clone();
        session.set_observer(Box::new(move |e| match e {
            SessionEvent::TranscriptDropped { path, cause } => seen
                .borrow_mut()
                .push(format!("dropped {} {cause}", path.display())),
            SessionEvent::Answered { record_bytes, .. } => {
                seen.borrow_mut().push(format!("answered {}", record_bytes.is_some()))
            }
            _ => {}
        }));
        for _ in 0..5 {
            assert_eq!(session.send("auto.").unwrap().status, Status::Error);
        }
        assert_eq!(sink.text().lines().count(), 2);
        assert_eq!(
            *events.borrow(),
            [
                "answered true",
                "answered true",
                "dropped /out/progress/ec-transcript.jsonl No space left on device",
                "answered false",
                "answered false",
                "answered false",
            ]
        );
        assert!(session.transcript_dropped());
    }

    #[test]
    fn a_failed_full_write_fails_naming_the_path() {
        let dir = tempfile::tempdir().unwrap();
        let answer = crate::easycrypt::transcript::tests::answer_with_goals(1, 10);
        let sink = TestSink::new(1);
        let mut session = fake_session(dir.path(), &answer, &sink, EcTranscriptMode::Full);
        session.send("auto.").unwrap();
        let err = session.send("auto.").err().unwrap();
        assert!(matches!(err, SessionError::Transcript { .. }), "{err}");
        let text = err.to_string();
        assert!(text.contains("/out/progress/ec-transcript.jsonl"), "{text}");
        assert!(text.contains("No space left on device"), "{text}");
    }

    fn session_in(dir: &Path) -> Option<Session> {
        if !json_binary_configured() {
            eprintln!("{ENV_VAR} not set, skipping the EasyCrypt session test");
            return None;
        }
        Some(Session::start(dir).expect("the configured EasyCrypt starts"))
    }

    #[test]
    fn send_error_undo_and_interrupt() {
        let dir = tempfile::tempdir().unwrap();
        let Some(mut ec) = session_in(dir.path()) else {
            return;
        };
        assert!(ec.goals().is_empty());

        // send
        let r = ec.send("lemma l (x : int) : x = x.").unwrap().clone();
        assert_eq!(r.status, Status::Ok);
        let opened = r.state;
        assert_eq!(ec.goals().len(), 1);
        assert_eq!(ec.goals()[0].concl.pp, "x = x");

        // error: the goals stay, no undo level is pushed
        let r = ec.send("by exact foo.").unwrap();
        assert_eq!(r.status, Status::Error);
        assert!(r.error.is_some());
        assert_eq!(r.state, opened);
        assert_eq!(ec.goals().len(), 1);

        // a success, then undo to before it
        let r = ec.send("proof.").unwrap();
        assert_eq!(r.status, Status::Ok);
        let r = ec.send("trivial.").unwrap();
        assert!(r.proof.as_ref().unwrap().goals.is_empty());
        let r = ec.undo_to(opened).unwrap();
        assert_eq!(r.state, opened);
        assert_eq!(ec.goals().len(), 1);
        assert_eq!(ec.transcript().len(), 5);

        // interrupt: `do !` on a tactic that always succeeds never ends, so the timeout fires
        ec.set_timeout(Duration::from_millis(500));
        let r = ec.send("by do ! (have _ : true by trivial); trivial.").unwrap();
        assert_eq!(r.status, Status::Interrupted);
        assert_eq!(r.state, opened);
        assert_eq!(ec.goals().len(), 1, "the goals are kept");

        // and the session goes on
        ec.set_timeout(Duration::from_secs(60));
        let r = ec.send("trivial.").unwrap();
        assert_eq!(r.status, Status::Ok);
        assert!(r.proof.as_ref().unwrap().goals.is_empty());
    }
}
