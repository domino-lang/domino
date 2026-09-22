# Story 01 — cvc5-rs solver backend with incremental push/pop

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** nothing. Can be done first, or in parallel with stories 02 and 04.
**Blocks:** story 06.

---

## 1. Why this story exists

The debugger is an *interactive* solver client. It walks an execution tree and asks the solver,
at every branching point, "is this branch reachable given everything asserted so far?". That
needs three things the current solver layer does not have:

1. **`push` / `pop`**, so the assertion stack can mirror the execution tree instead of restarting
   the solver for every query. `src/gamehops/equivalence/verify_fn.rs:474` (`verify_with_solver`)
   today spawns a *fresh* solver process per claim, writes everything, fires one `check-sat`, and
   drops it. That is fine for `prove`; it would be hopeless for thousands of tree queries.
2. **Option setting** at runtime, for the per-query timeout (`tlimit-per`).
3. The **cvc5-rs** backend the owner asked for in `docs/symbolic-execution-plan.md`
   ("For interactive interaction with solver use cvc5-rs crate which is cvc5 bindings for rust!").

## 2. Key insight — do not rewrite the SMT emission

The natural fear with native bindings is that we would have to abandon the textual `SmtExpr`
representation and build cvc5 `Term`s programmatically. **We do not.** The `cvc5` crate has a
`parser` feature exposing `InputParser` in *incremental string* mode:

```rust
parser.set_inc_str_input(InputLanguage::Smtlib2, "domino");   // once
parser.append_inc_str_input("(declare-const x Int)\n");        // per write
while let Some(cmd) = parser.next_command()? {                 // parse
    let out: String = cmd.invoke(&mut solver, &mut symbol_manager);  // execute
}
```

`Command::invoke` returns the command's textual output — which is exactly `"sat"` / `"unsat"` /
`"unknown"` for `(check-sat)` and the model s-expression for `(get-model)`. So the whole existing
`SmtExpr → String` pipeline is reused unchanged, and the transcript is simply everything we
appended.

Relevant API (crate `cvc5` 0.4.1, homepage <https://github.com/cvc5/cvc5-rs>):

- `TermManager`, `Solver<'tm>`, `SymbolManager`, `InputParser<'tm>`, `Command`, `InputLanguage`
- `InputParser::new(solver, sm)`, `set_inc_str_input`, `append_inc_str_input`, `next_command`,
  `done`, `get_solver`, `get_symbol_manager`
- `Command::invoke(&self, solver: &mut Solver, sm: &mut SymbolManager) -> String`, `Command::name`

**Constraint to respect:** `Solver`, `InputParser` and `Command` are `!Send` and `!Sync`. The
debugger must therefore be single-threaded. `prove` keeps the process backend and its rayon
fan-out (`src/gamehops/equivalence/verify_fn.rs:143`); do not try to make the cvc5 backend work
under rayon.

## 3. What exists today

`src/util/smtsolver/mod.rs` (the whole file is ~72 lines):

```rust
pub enum SmtSolverResponse { Sat, Unsat, Unknown }

pub trait SmtSolverBackend {
    type Solver: SmtSolver;
    fn new_smtsolver(&self) -> Result<Self::Solver>;
    fn new_smtsolver_with_transcript<W: std::io::Write + Send + Sync + 'static>(
        &self, write: W,
    ) -> Result<Self::Solver>;
}

pub trait SmtSolver: fmt::Write {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()>;
    fn check_sat(&mut self) -> Result<SmtSolverResponse>;
    fn get_model(&mut self) -> Result<(String, SmtModel)>;
    fn close(&mut self);
}
```

`src/util/smtsolver/process.rs` implements it over a child process
(`src/util/process.rs::Communicator`), with `SolverVariant::{Cvc4, Cvc5, Z3}` and the
`--produce-models --arrays-exp` flags for cvc5.

Model parsing already exists: `src/util/smtparser/` (`model.rs`, `functions.rs`,
`implementation.rs`) producing `crate::util::smtmodel::SmtModel`. `Communicator::get_model`
writes `(get-model)` and calls `self.0.read_model()`.

Cargo features today (root `Cargo.toml`): `default = ["process-solver"]`,
`process-solver = ["dep:clap", "dep:expectrl", "dep:subprocess"]`, `zipfile = [...]`.

`flake.nix` already provides `pkgs.cvc5` (lines ~150 and ~180) as a runtime binary.

## 4. Work to do

### 4.1 Extend the `SmtSolver` trait

In `src/util/smtsolver/mod.rs`:

```rust
pub trait SmtSolver: fmt::Write {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()>;
    fn check_sat(&mut self) -> Result<SmtSolverResponse>;
    fn get_model(&mut self) -> Result<(String, SmtModel)>;

    /// Push one assertion level.
    fn push(&mut self) -> Result<()>;
    /// Pop one assertion level.
    fn pop(&mut self) -> Result<()>;
    /// `(set-option :<key> <value>)`.
    fn set_option(&mut self, key: &str, value: &str) -> Result<()>;

    fn close(&mut self);
}
```

Implement all three for `process::Communicator` as plain writes (`(push 1)`, `(pop 1)`,
`(set-option :key value)`). `prove` never calls them, so its behaviour is unchanged.

### 4.2 New backend module `src/util/smtsolver/cvc5lib.rs`

Behind `#[cfg(feature = "cvc5-lib")]`, gated from `src/util/smtsolver/mod.rs`.

```rust
pub struct Cvc5LibBackend { pub produce_models: bool, pub tlimit_per_ms: Option<u64> }

pub struct Cvc5LibSolver { /* TermManager + Solver + SymbolManager + InputParser + transcript */ }
```

Design notes:

- The `Solver<'tm>` borrows a `TermManager`. The simplest sound arrangement is to leak or
  `Box::leak` a `TermManager` per solver instance (one per `debug` run — cheap and unambiguous),
  or use a self-referential wrapper. Prefer the leak: it keeps lifetimes out of the public type
  and there is exactly one solver per run.
- `set_inc_str_input(InputLanguage::Smtlib2, "domino-debug")` once at construction.
- `write_smt` / `write_str`: append the text to the parser, tee it to the optional transcript
  writer, then drain `next_command()` in a loop invoking each `Command`. Keep the returned
  strings for the last command so `check_sat` / `get_model` can read them.
  - Careful: a partially-written s-expression must not be parsed. `next_command()` returns
    `Ok(None)` when the input is incomplete, so a drain loop that stops on `Ok(None)` is correct
    — just make sure the buffer is not discarded between writes.
- `check_sat`: append `(check-sat)`, drain, and map the invoke output (`"sat"` / `"unsat"` /
  `"unknown"`, possibly with whitespace) to `SmtSolverResponse`. An unrecognised or
  `(error ...)` output becomes `Error::SolverError` (already exists in
  `src/util/smtsolver/error.rs`).
- `get_model`: append `(get-model)`, drain, feed the returned string through the existing
  `src/util/smtparser` to produce `(String, SmtModel)` — the same contract as
  `Communicator::get_model`.
- Options set at construction: `produce-models = true`, `incremental = true`; and
  `tlimit-per = <ms>` when `tlimit_per_ms` is `Some`. Expose `set_option` so the driver can
  change `tlimit-per` later.
- `close`: drop everything; there is no process to reap.

### 4.3 Cargo and build plumbing

Root `Cargo.toml`:

```toml
[features]
default = ["process-solver"]
process-solver = ["dep:clap", "dep:expectrl", "dep:subprocess"]
cvc5-lib = ["dep:cvc5"]
zipfile = ["dep:zip"]

[dependencies]
cvc5 = { version = "0.4", features = ["static", "parser"], optional = true }
```

`static` builds cvc5 from source (needs a C/C++ toolchain, CMake ≥ 3.16 and libclang for
bindgen). If that turns out to be too heavy for the dev loop, the alternative documented by the
crate is to drop `static` and point `CVC5_LIB_DIR` / `CVC5_INCLUDE_DIR` at a prebuilt cvc5 —
`flake.nix` already has `pkgs.cvc5`. Pick one, make it work, and **document what you picked** in
`Readme.md` and in the `flake.nix` dev shell (add `cmake`, `libclang`/`llvmPackages.libclang`,
and the `LIBCLANG_PATH` / `CVC5_*` env vars as needed).

The default build must stay unchanged: `cargo build --workspace` with no extra features must not
require cvc5 headers.

## 5. Acceptance criteria

- [ ] `SmtSolver` has `push`, `pop`, `set_option`; `process::Communicator` implements them.
- [ ] `cargo build --workspace` (no extra features) succeeds and does not pull in `cvc5`.
- [ ] `cargo build --workspace --features cvc5-lib` succeeds, with build prerequisites documented.
- [ ] `cargo test --workspace --features cvc5-lib` passes a new unit test that:
      declares a const → asserts something satisfiable → `check_sat` = `Sat` → `push` → asserts a
      contradiction → `check_sat` = `Unsat` → `pop` → `check_sat` = `Sat` → `get_model` returns a
      string that parses into an `SmtModel` via `src/util/smtparser`.
- [ ] A second unit test proves the transcript writer receives every command in order, including
      `(push 1)` / `(pop 1)` / `(check-sat)`.
- [ ] `scripts/test-known-examples.sh` behaviour is untouched (this story does not change any
      code path `prove` executes beyond adding trait methods with process implementations).

## 6. How to verify

```bash
cargo build --workspace
cargo test  --workspace
cargo build --workspace --features cvc5-lib
cargo test  --workspace --features cvc5-lib

# sanity: prove still works on something tiny
cd test-projects/test-loopunroll && cargo run --bin domino -- prove
```

**Do not** run `prove` on `example-projects/4WHS` or `example-projects/yao` — see the testing
strategy in `docs/stories/00-overview.md`. Nothing in this story needs a large project.

## 7. Notes / risks

- The `static` cvc5 build is slow on a cold cache (several minutes). Build it once, early, so it
  is not mistaken for a hang later.
- If `InputParser`'s incremental mode turns out to choke on comments (`SmtExpr::Comment`), strip
  or convert comments before appending, and note it in "State handed to the next story".
- `Solver` being `!Send` means `Cvc5LibSolver` cannot satisfy the `Sync` bounds
  `EquivalenceSmtDriver` requires. Do **not** try to make `prove` use it; the debugger gets its
  own driver in story 06.

## 8. State handed to the next story

Story 06 will rely on:

- `SmtSolver::{push, pop, set_option}` in `src/util/smtsolver/mod.rs`.
- `src/util/smtsolver/cvc5lib.rs` exporting `Cvc5LibBackend` (implementing `SmtSolverBackend`)
  and `Cvc5LibSolver` (implementing `SmtSolver`), behind feature `cvc5-lib`.
- `Cvc5LibBackend::new_smtsolver_with_transcript(writer)` producing a solver that tees every
  command to `writer` — that is the debugger's `transcript.smt2`.
- Whatever build prerequisites you settled on, documented in `Readme.md` / `flake.nix`.

Record here anything surprising you hit (API quirks, feature-flag names, `!Send` fallout) so the
next cold session does not rediscover it.

---

### Implemented — see `docs/stories/01-cvc5-backend-IMPLEMENTATION-REPORT.md` for the full handover.

Surprises worth knowing before touching this code:

- **The incremental parser is single-shot.** After `next_command()` returns `Ok(None)`, a further
  `append_inc_str_input` aborts the process (*"Must call setIncrementalStringInput prior…"*). Fix:
  `Cvc5LibSolver::feed` keeps its own `pending` buffer, only feeds cvc5 whole top-level commands,
  and re-calls `set_inc_str_input` before every append. The story's "keep the buffer across
  writes / stop on Ok(None)" advice does not work as written.
- Enum variant is **`InputLanguage::SmtLib26`**, not `Smtlib2`.
- `;` comments are fine — no stripping needed.
- `Cvc5LibSolver` is `!Send`/`!Sync` (confirmed) → needs its own driver in story 06.
- Build: `cvc5` crate with `["static","parser"]` **plus** `CVC5_LIB_DIR` pointing at a prebuilt
  **non-GPL** static release (the GPL one needs extra `cln`/`cocoa`/`glpk` link libs). bindgen
  needs `LIBCLANG_PATH`; a headers-less libclang also needs
  `BINDGEN_EXTRA_CLANG_ARGS=-I<gcc>/include`. All wired by `scripts/setup-cvc5-lib.sh`.
- `flake.nix` `devShells.cvc5-lib` was added but **not tested** (no nix on the dev machine).
