// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native cvc5 solver backend built on the `cvc5` crate (cvc5-rs).
//!
//! Unlike [`super::process`], this backend does not spawn a child process. It drives an in-process
//! cvc5 [`Solver`] through the crate's incremental-string [`InputParser`]: every chunk of SMT-LIB
//! text we would have written to a solver's stdin is instead appended to the parser and the
//! resulting [`Command`]s are invoked directly. The existing `SmtExpr -> String` pipeline is reused
//! verbatim; the transcript is simply everything we appended.
//!
//! ## `!Send` / `!Sync`
//!
//! `cvc5::Solver`, `cvc5::InputParser` and `cvc5::Command` are `!Send` and `!Sync` (they hold `Rc`
//! and raw pointers). [`Cvc5LibSolver`] is therefore `!Send` / `!Sync` as well and cannot be used
//! under rayon. `domino prove` keeps the process backend; this backend is for the single-threaded
//! `domino debug` driver.
//!
//! ## Build prerequisites
//!
//! Behind the `cvc5-lib` cargo feature, which pulls in `cvc5` with `features = ["static",
//! "parser"]`. Building it needs a prebuilt static cvc5 and a working libclang for bindgen — see
//! `scripts/setup-cvc5-lib.sh` and the "cvc5-lib feature" section of `Readme.md`.

use std::fmt::{self, Write as _};

use cvc5::{InputLanguage, InputParser, Solver, SymbolManager, TermManager};

use crate::util::smtmodel::SmtModel;
use crate::util::smtparser::parse_model;
use crate::writers::smt::exprs::SmtExpr;

use super::{Error, Result, SmtSolver, SmtSolverBackend, SmtSolverResponse};

/// Backend handing out [`Cvc5LibSolver`] instances.
pub struct Cvc5LibBackend {
    /// Sets `:produce-models` on every solver created.
    pub produce_models: bool,
    /// When `Some`, sets `:tlimit-per` (per-query timeout, milliseconds) on every solver created.
    pub tlimit_per_ms: Option<u64>,
}

impl Cvc5LibBackend {
    pub fn new(produce_models: bool, tlimit_per_ms: Option<u64>) -> Self {
        Self {
            produce_models,
            tlimit_per_ms,
        }
    }
}

impl SmtSolverBackend for Cvc5LibBackend {
    type Solver = Cvc5LibSolver;

    fn new_smtsolver(&self) -> Result<Self::Solver> {
        Cvc5LibSolver::new(self.produce_models, self.tlimit_per_ms, None)
    }

    fn new_smtsolver_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self,
        writer: W,
    ) -> Result<Self::Solver> {
        Cvc5LibSolver::new(
            self.produce_models,
            self.tlimit_per_ms,
            Some(Box::new(writer)),
        )
    }
}

type Transcript = Box<dyn std::io::Write + Send + Sync + 'static>;

/// An in-process cvc5 solver driven through the incremental-string parser.
pub struct Cvc5LibSolver {
    // `parser` borrows a `TermManager` that we `Box::leak` in `new`. There is exactly one solver
    // per `debug` run (a handful per test), so the leak is bounded and keeps the lifetime out of
    // the public type. `symbol_manager` is an `Rc` handle onto the same table the parser mutates.
    parser: InputParser<'static>,
    symbol_manager: SymbolManager,
    transcript: Option<Transcript>,
    /// SMT-LIB text that has been written but does not yet form a whole top-level command.
    /// Carried across `feed` calls so a write that splits a command mid-way is not lost — see
    /// the note on `set_inc_str_input` below.
    pending: String,
    /// Textual output of the most recent non-empty command invocation (e.g. `"sat"` for
    /// `(check-sat)`, the model s-expression for `(get-model)`).
    last_output: String,
}

impl Cvc5LibSolver {
    fn new(
        produce_models: bool,
        tlimit_per_ms: Option<u64>,
        transcript: Option<Transcript>,
    ) -> Result<Self> {
        let tm: &'static TermManager = Box::leak(Box::new(TermManager::new()));
        let mut solver = Solver::new(tm);

        // These are all legal before `(set-logic ...)`. We deliberately do *not* set the logic
        // here: the emitted SMT starts with `(set-logic ALL)` and cvc5 rejects setting it twice.
        solver.set_option(
            "produce-models",
            if produce_models { "true" } else { "false" },
        );
        solver.set_option("incremental", "true");
        // Match the process backend's `--arrays-exp` (see `super::process::Communicator::new_cvc5`).
        // Games with tables/arrays emit constant arrays (`(as const (Array ...))`, kind STORE_ALL);
        // without this cvc5 rejects them with "Cannot handle assertion with term of kind STORE_ALL".
        // Must be set before `(set-logic ...)`, which is the first thing the emitted SMT does.
        solver.set_option("arrays-exp", "true");
        if let Some(ms) = tlimit_per_ms {
            solver.set_option("tlimit-per", &ms.to_string());
        }

        let sm = SymbolManager::new(tm);
        let parser = InputParser::new(solver, Some(&sm));
        let symbol_manager = parser.get_symbol_manager();

        Ok(Self {
            parser,
            symbol_manager,
            transcript,
            pending: String::new(),
            last_output: String::new(),
        })
    }

    /// Tee `text` to the transcript, then hand every *complete* top-level command it completes to
    /// cvc5 and invoke it.
    ///
    /// ## Why this is not just `append_inc_str_input` + drain
    ///
    /// In this cvc5 version the incremental parser is single-shot: once `next_command` has drained
    /// the appended input and returned `Ok(None)`, a further `append_inc_str_input` fails with
    /// *"Must call setIncrementalStringInput prior to using appendIncrementalStringInput"*. The
    /// working pattern is to call `set_inc_str_input` again before every append — but that also
    /// discards whatever partial s-expression was still buffered. So we keep our own `pending`
    /// buffer, only ever feed cvc5 a run of whole commands (`complete_prefix_len`), and hold the
    /// incomplete tail back for the next call.
    fn feed(&mut self, text: &str) -> Result<()> {
        if let Some(w) = self.transcript.as_mut() {
            w.write_all(text.as_bytes())?;
        }
        self.pending.push_str(text);

        let complete = complete_prefix_len(&self.pending);
        if complete == 0 {
            return Ok(());
        }
        let chunk: String = self.pending.drain(..complete).collect();

        self.parser
            .set_inc_str_input(InputLanguage::SmtLib26, "domino-debug");
        self.parser.append_inc_str_input(&chunk);

        loop {
            match self.parser.next_command() {
                Ok(Some(cmd)) => {
                    let out = cmd.invoke(self.parser.get_solver(), &mut self.symbol_manager);
                    let trimmed = out.trim();
                    if trimmed.is_empty() {
                        continue;
                    }
                    if trimmed.starts_with("(error \"") {
                        return Err(Error::SolverError(out));
                    }
                    self.last_output = out;
                }
                Ok(None) => break,
                Err(msg) => return Err(Error::SolverError(msg)),
            }
        }

        // Don't let inter-command whitespace pile up in the buffer forever.
        if self.pending.trim().is_empty() {
            self.pending.clear();
        }
        Ok(())
    }
}

/// Length of the longest prefix of `buf` that contains only whole top-level s-expressions (with
/// any interleaved whitespace and `;` comments). `0` means no complete command yet.
///
/// Tracks nesting depth while skipping over `"string literals"` (`""` escapes a quote),
/// `|quoted symbols|` and `; line comments` so a paren inside any of those does not move the depth.
fn complete_prefix_len(buf: &str) -> usize {
    let bytes = buf.as_bytes();
    let mut depth: i32 = 0;
    let mut seen_open = false;
    let mut boundary = 0;
    let mut i = 0;

    while i < bytes.len() {
        match bytes[i] {
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                loop {
                    if i >= bytes.len() {
                        return boundary; // unterminated string: wait for more input
                    }
                    if bytes[i] == b'"' {
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2; // escaped quote
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    i += 1;
                }
            }
            b'|' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                if i >= bytes.len() {
                    return boundary; // unterminated quoted symbol
                }
                i += 1;
            }
            b'(' => {
                depth += 1;
                seen_open = true;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
                if depth < 0 {
                    // malformed input; let cvc5 produce the error message
                    return buf.len();
                }
                if depth == 0 && seen_open {
                    boundary = i;
                    seen_open = false;
                }
            }
            _ => {
                i += 1;
            }
        }
    }
    boundary
}

impl SmtSolver for Cvc5LibSolver {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()> {
        let mut buffer = String::new();
        write!(buffer, "{}", expr.into())?;
        self.feed(&buffer)
    }

    fn check_sat(&mut self) -> Result<SmtSolverResponse> {
        self.feed("\n(check-sat)\n")?;
        match self.last_output.trim() {
            "sat" => Ok(SmtSolverResponse::Sat),
            "unsat" => Ok(SmtSolverResponse::Unsat),
            // cvc5 reports `unknown` on its own, and `unknown (TIMEOUT)` /
            // `unknown (INCOMPLETE)` etc. when it can name the reason (e.g. a
            // `tlimit-per` timeout).
            s if s == "unknown" || s.starts_with("unknown (") => Ok(SmtSolverResponse::Unknown),
            other => Err(Error::SolverError(format!(
                "unexpected (check-sat) output: {other:?}"
            ))),
        }
    }

    fn get_model(&mut self) -> Result<(String, SmtModel)> {
        self.feed("\n(get-model)\n")?;
        let modelstring = self.last_output.clone();
        let (model, _consumed) = parse_model(&modelstring)
            .map_err(|err| Error::SolverError(format!("could not parse model: {err}")))?;
        Ok((modelstring, model))
    }

    fn push(&mut self) -> Result<()> {
        self.feed("\n(push 1)\n")
    }

    fn pop(&mut self) -> Result<()> {
        self.feed("\n(pop 1)\n")
    }

    fn set_option(&mut self, key: &str, value: &str) -> Result<()> {
        self.feed(&format!("\n(set-option :{key} {value})\n"))
    }

    fn close(&mut self) {
        if let Some(w) = self.transcript.as_mut() {
            let _ = w.flush();
        }
    }
}

impl fmt::Write for Cvc5LibSolver {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.feed(s).map_err(|_| fmt::Error)
    }
}

#[cfg(test)]
mod test {
    use std::sync::{Arc, Mutex};

    use super::*;

    /// A `Write` we can still read back after handing it to the solver.
    #[derive(Clone, Default)]
    struct SharedWriter(Arc<Mutex<Vec<u8>>>);

    impl SharedWriter {
        fn contents(&self) -> String {
            String::from_utf8(self.0.lock().unwrap().clone()).unwrap()
        }
    }

    impl std::io::Write for SharedWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn push_pop_check_sat_and_model() {
        let backend = Cvc5LibBackend::new(true, None);
        let mut solver = backend.new_smtsolver().unwrap();

        solver.write_smt(("set-logic", "ALL")).unwrap();
        solver
            .write_smt(SmtExpr::Comment("a satisfiable base".to_string()))
            .unwrap();
        solver.write_smt(("declare-const", "x", "Int")).unwrap();
        solver
            .write_smt(vec![
                SmtExpr::from("assert"),
                vec![SmtExpr::from(">"), "x".into(), "0".into()].into(),
            ])
            .unwrap();

        assert_eq!(solver.check_sat().unwrap(), SmtSolverResponse::Sat);

        solver.push().unwrap();
        solver
            .write_smt(vec![
                SmtExpr::from("assert"),
                vec![SmtExpr::from("<"), "x".into(), "0".into()].into(),
            ])
            .unwrap();
        assert_eq!(solver.check_sat().unwrap(), SmtSolverResponse::Unsat);

        solver.pop().unwrap();
        assert_eq!(solver.check_sat().unwrap(), SmtSolverResponse::Sat);

        let (modelstring, model) = solver.get_model().unwrap();
        assert!(
            modelstring.contains('x'),
            "model string should mention x: {modelstring:?}"
        );
        assert!(
            model.get_value("x").is_some(),
            "parsed model should have an entry for x: {model:?}"
        );

        solver.close();
    }

    #[test]
    fn transcript_receives_every_command_in_order() {
        let sink = SharedWriter::default();
        let backend = Cvc5LibBackend::new(false, None);
        let mut solver = backend.new_smtsolver_with_transcript(sink.clone()).unwrap();

        solver.write_smt(("set-logic", "ALL")).unwrap();
        solver.write_smt(("declare-const", "b", "Bool")).unwrap();
        solver.check_sat().unwrap();
        solver.push().unwrap();
        solver
            .write_smt(vec![SmtExpr::from("assert"), "b".into()])
            .unwrap();
        solver.check_sat().unwrap();
        solver.pop().unwrap();
        solver.set_option("tlimit-per", "1000").unwrap();
        solver.check_sat().unwrap();
        solver.close();

        // Normalise the pretty-printer's line breaks / indentation before checking order.
        let text = sink
            .contents()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let markers = [
            "(set-logic ALL)",
            "(declare-const b Bool)",
            "(check-sat)",
            "(push 1)",
            "(assert b)",
            "(check-sat)",
            "(pop 1)",
            "(set-option :tlimit-per 1000)",
            "(check-sat)",
        ];
        let mut cursor = 0;
        for marker in markers {
            match text[cursor..].find(marker) {
                Some(offset) => cursor += offset + marker.len(),
                None => panic!("transcript missing {marker:?} (in order) in:\n{text}"),
            }
        }
    }

    #[test]
    fn partial_writes_are_buffered_until_a_command_completes() {
        use std::fmt::Write as _;

        let backend = Cvc5LibBackend::new(true, None);
        let mut solver = backend.new_smtsolver().unwrap();

        // Feed a single command in fragments that split it mid-s-expression, plus a `;` comment.
        solver
            .write_str("(set-logic ALL)\n; a comment\n(declare-const ")
            .unwrap();
        solver.write_str("n Int)\n(assert (> n ").unwrap();
        solver.write_str("41))\n").unwrap();
        solver.write_str("(assert (< n 43))\n").unwrap();

        assert_eq!(solver.check_sat().unwrap(), SmtSolverResponse::Sat);
        let (_, model) = solver.get_model().unwrap();
        assert_eq!(model.get_value_as_int("n"), Some(42));
    }
}
