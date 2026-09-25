// SPDX-License-Identifier: MIT OR Apache-2.0

//! A live `easycrypt cli -json` process (story 26 §3.1).
//!
//! [`Session::send`] writes one sentence and reads the one JSON line EasyCrypt answers with
//! (`easycrypt/doc/json-output.md`). The state of the session after the sentence is the
//! returned [`Response`]; [`Session::undo_to`] goes back to an earlier one in O(1). Every
//! exchange is kept in [`Session::transcript`], for story 27 to write to a file.
//!
//! The binary is found through the `DOMINO_EASYCRYPT` environment variable, falling back to
//! `easycrypt` on `PATH`, and is checked at startup: a binary that does not answer in
//! `domino-json/1` is refused with a message naming the variable and the branch of the
//! EasyCrypt clone that adds the format.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::Duration;

use thiserror::Error;

use super::json::{self, Goal, Response, Status, FORMAT_VERSION};

/// The environment variable naming the `-json`-capable EasyCrypt binary.
pub const ENV_VAR: &str = "DOMINO_EASYCRYPT";

/// The EasyCrypt clone branch that adds `cli -json` (story 25).
const JSON_BRANCH: &str = "amir/domino-easycrypt-integration";

/// How long a sentence may run before it is interrupted, unless [`Session::set_timeout`] says
/// otherwise.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(600);

/// How long the answer to a `SIGINT` may take.
const INTERRUPT_GRACE: Duration = Duration::from_secs(30);

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
    /// is a transcript sink (the record is on disk already).
    Answered {
        sentence: &'a str,
        response: &'a Response,
        elapsed: Duration,
        record_bytes: Option<usize>,
    },
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
    observer: Option<Box<dyn FnMut(&SessionEvent<'_>)>>,
}

/// Where [`Session::send`] appends every exchange, one JSON object per line: `{"file": <tag>,
/// "ctx": <the caller's note>, "sentence": <the sentence>, "ms": <how long EasyCrypt took>,
/// "response": <EasyCrypt's answer, verbatim>}`.
struct TranscriptSink {
    writer: Box<dyn Write + Send>,
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
            observer: None,
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

    /// Appends every later exchange, with EasyCrypt's answer verbatim, to `writer` as one JSON
    /// line (`{"file": tag, "ctx": …, "sentence": …, "ms": …, "response": …}`): undone attempts included, goals
    /// included. This is `ec-transcript.jsonl` (story 27 §3.7).
    pub fn set_transcript_sink(&mut self, writer: Box<dyn Write + Send>, tag: &str) {
        self.sink = Some(TranscriptSink {
            writer,
            tag: tag.to_string(),
            context: String::new(),
        });
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

    /// Waits for the next line, up to the timeout, reporting [`SessionEvent::Waiting`] on the way.
    fn wait_line(
        &mut self,
        sentence: &str,
        began: std::time::Instant,
    ) -> Result<std::io::Result<Line>, RecvTimeoutError> {
        if self.observer.is_none() {
            return self.lines.recv_timeout(self.timeout);
        }
        loop {
            let left = self.timeout.saturating_sub(began.elapsed());
            if left.is_zero() {
                return Err(RecvTimeoutError::Timeout);
            }
            match self.lines.recv_timeout(left.min(WAIT_TICK)) {
                Err(RecvTimeoutError::Timeout) => self.notify(&SessionEvent::Waiting {
                    sentence,
                    elapsed: began.elapsed(),
                }),
                other => return other,
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
    /// timeout is interrupted, and the answer is then `Status::Interrupted`.
    pub fn send(&mut self, sentence: &str) -> Result<&Response, SessionError> {
        let began = std::time::Instant::now();
        self.notify(&SessionEvent::Sending { sentence });
        self.write_line(sentence)?;
        let line = match self.wait_line(sentence, began) {
            Ok(line) => line,
            Err(RecvTimeoutError::Timeout) => {
                self.interrupt()?;
                self.lines
                    .recv_timeout(INTERRUPT_GRACE)
                    .map_err(|_| SessionError::Unresponsive {
                        sentence: sentence.to_string(),
                    })?
            }
            Err(RecvTimeoutError::Disconnected) => {
                return Err(SessionError::Closed {
                    sentence: sentence.to_string(),
                })
            }
        };
        let line = line?;
        let mut record_bytes = None;
        if let Some(sink) = &mut self.sink {
            let record = format!(
                "{{\"file\":{},\"ctx\":{},\"sentence\":{},\"ms\":{},\"response\":{}}}\n",
                serde_json::Value::from(sink.tag.as_str()),
                serde_json::Value::from(sink.context.as_str()),
                serde_json::Value::from(sentence),
                began.elapsed().as_millis(),
                line.raw.trim_end()
            );
            sink.writer.write_all(record.as_bytes())?;
            record_bytes = Some(record.len());
        }
        let response = line.parsed.map_err(|source| SessionError::BadAnswer {
            sentence: sentence.to_string(),
            source,
        })?;
        // A goal is hundreds of kilobytes of JSON: only the newest answer keeps its goals.
        if let Some(previous) = self.transcript.last_mut() {
            previous.response.proof = None;
        }
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
            };
            // `notify` borrows `self` mutably: take the observer out for the call
            if let Some(mut observer) = self.observer.take() {
                observer(&event);
                self.observer = Some(observer);
            }
        }
        Ok(&self.transcript.last().expect("just pushed").response)
    }

    /// Returns to the state whose answer said `state` (`undo <state>.`).
    pub fn undo_to(&mut self, state: u64) -> Result<&Response, SessionError> {
        self.send(&format!("undo {state}."))
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
mod tests {
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
