# Story 01 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. Not yet committed.

This is the "State handed to the next story" for stories 06 (and anyone touching the solver layer).
Read it together with `docs/stories/01-cvc5-backend.md`.

---

## 1. What landed

| File | Change |
|---|---|
| `src/util/smtsolver/mod.rs` | `SmtSolver` trait gains `push`, `pop`, `set_option`. New `#[cfg(feature = "cvc5-lib")] pub mod cvc5lib;`. |
| `src/util/smtsolver/process.rs` | `Communicator` implements `push`/`pop`/`set_option` as plain writes (`(push 1)`, `(pop 1)`, `(set-option :k v)`). `prove` never calls them. |
| `src/util/smtsolver/cvc5lib.rs` | **new.** `Cvc5LibBackend` (impls `SmtSolverBackend`) + `Cvc5LibSolver` (impls `SmtSolver` + `fmt::Write`), behind `cvc5-lib`. 3 unit tests. |
| `Cargo.toml` | `cvc5-lib = ["dep:cvc5"]` feature; `cvc5 = { version = "0.4", features = ["static", "parser"], optional = true }`. |
| `Cargo.lock` | now records `cvc5` 0.4.1 + `cvc5-sys` 0.4.0 + bindgen/clang-sys/etc. (optional deps are always in the lock; a default build does **not** compile them). |
| `scripts/setup-cvc5-lib.sh` | **new.** fetches prebuilt static cvc5 + libclang into `~/.cache/domino`, writes `~/.cache/domino/cvc5-lib-env.sh`. |
| `Readme.md` | "`cvc5-lib` feature" section under Installation. |
| `flake.nix` | new `devShells.cvc5-lib` (toolchain + `pkgs.llvmPackages.libclang` + `LIBCLANG_PATH`). **Untested — no nix on the dev machine** (see §5). |

## 2. Public surface for story 06

```rust
// src/util/smtsolver/mod.rs
pub trait SmtSolver: fmt::Write {
    fn write_smt<I: Into<SmtExpr>>(&mut self, expr: I) -> Result<()>;
    fn check_sat(&mut self) -> Result<SmtSolverResponse>;
    fn get_model(&mut self) -> Result<(String, SmtModel)>;
    fn push(&mut self) -> Result<()>;                       // NEW: (push 1)
    fn pop(&mut self) -> Result<()>;                        // NEW: (pop 1)
    fn set_option(&mut self, key: &str, value: &str) -> Result<()>;  // NEW: (set-option :key value)
    fn close(&mut self);
}

// src/util/smtsolver/cvc5lib.rs   (feature = "cvc5-lib")
pub struct Cvc5LibBackend { pub produce_models: bool, pub tlimit_per_ms: Option<u64> }
impl Cvc5LibBackend { pub fn new(produce_models: bool, tlimit_per_ms: Option<u64>) -> Self }
impl SmtSolverBackend for Cvc5LibBackend { type Solver = Cvc5LibSolver; /* new_smtsolver, new_smtsolver_with_transcript */ }

pub struct Cvc5LibSolver { /* !Send, !Sync */ }
impl SmtSolver for Cvc5LibSolver { ... }
impl std::fmt::Write for Cvc5LibSolver { ... }
```

- `new_smtsolver_with_transcript(writer)` tees **every** byte appended (including `(push 1)` /
  `(pop 1)` / `(check-sat)` / `(get-model)` / `(set-option …)`) to `writer` before it reaches
  cvc5. That is the debugger's `transcript.smt2`.
- Options set at construction: `:produce-models` (per `produce_models`), `:incremental true`,
  and `:tlimit-per <ms>` when `tlimit_per_ms` is `Some`. Change `tlimit-per` later with
  `solver.set_option("tlimit-per", "…")`.
- `check_sat` maps `sat`/`unsat`/`unknown` → `SmtSolverResponse`; anything else (incl.
  `(error "…")`) → `Error::SolverError`.
- `get_model` feeds `(get-model)` and runs the result through `crate::util::smtparser::parse_model`
  — same `(String, SmtModel)` contract as `process::Communicator::get_model`.

## 3. API quirks discovered (important — do not rediscover)

### 3.1 The incremental parser is single-shot per `set_inc_str_input`

The story's suggested loop ("append, then drain `next_command()` until `Ok(None)`, keep the buffer
across writes") **does not work** with `cvc5` 0.4.1 / cvc5 1.3.x. Once `next_command()` has
consumed the appended input and returned `Ok(None)`, the next `append_inc_str_input` aborts the
process with:

```
cvc5: error: Must call setIncrementalStringInput prior to using appendIncrementalStringInput
```

The working pattern (and what `Cvc5LibSolver::feed` does):

1. keep our **own** `pending: String` buffer;
2. on each write, append to `pending`, then compute the longest prefix that is only *whole*
   top-level s-expressions (`complete_prefix_len`, which skips `"strings"`, `|quoted symbols|`
   and `; comments`);
3. `set_inc_str_input(SmtLib26, "domino-debug")` **again**, `append_inc_str_input(that prefix)`,
   drain `next_command()` to `Ok(None)`, invoking each command;
4. keep the incomplete tail in `pending` for next time.

Re-calling `set_inc_str_input` resets only the *parser input stream* — solver state (assertions,
push levels, options) persists across it. Verified with push/pop/check-sat/get-model.

### 3.2 `InputLanguage`

The variant is **`InputLanguage::SmtLib26`** (not `Smtlib2` as the story guessed). Others:
`Sygus21`, `Unknown`, `Last`.

### 3.3 Comments are fine

`SmtExpr::Comment` renders `;; text` at top level only. cvc5's parser eats `;` line comments
without complaint — no stripping needed. (Covered by the `partial_writes_*` test.)

### 3.4 `!Send` / `!Sync` confirmed

`cvc5::{Solver, InputParser, SymbolManager, TermManager}` are all `Rc`/raw-pointer based →
`Cvc5LibSolver` is `!Send`/`!Sync`. It therefore **cannot** satisfy the `SmtSolverBackend + Sync`
bound on `EquivalenceSmtDriver` (`src/gamehops/equivalence/verify_fn.rs:21`). Story 06 needs its
own single-threaded driver; do not try to route `prove` through this backend.

### 3.5 `TermManager` is leaked

`Cvc5LibSolver::new` does `Box::leak(Box::new(TermManager::new()))` to get a `&'static` for
`Solver<'tm>` / `InputParser<'tm>`, exactly as the story suggested. One leak per solver instance
(one per `debug` run; a few per test run). If story 06 ever creates many solvers in a loop,
revisit — but the epic design is one solver per `debug` invocation.

### 3.6 `Command::invoke` output

Empty string for `declare`/`assert`/`push`/`pop`/`set-option`; `"sat\n"` etc. for `check-sat`;
the model s-expression (`(\n(define-fun x () Int 1)\n)\n`) for `get-model`. `feed` tracks the last
non-empty output in `self.last_output`; `check_sat` / `get_model` read it right after their feed.

## 4. Build recipe (verified on the dev machine)

Default build is unchanged and needs nothing:

```bash
cargo build --workspace          # does NOT compile cvc5 / bindgen
cargo test  --workspace          # 92 pass (unchanged)
```

For the feature:

```bash
scripts/setup-cvc5-lib.sh                 # one-time; downloads to ~/.cache/domino
source ~/.cache/domino/cvc5-lib-env.sh    # sets CVC5_LIB_DIR / CVC5_INCLUDE_DIR / LIBCLANG_PATH / BINDGEN_EXTRA_CLANG_ARGS
cargo build --workspace --features cvc5-lib
cargo test  --workspace --features cvc5-lib   # 95 pass (92 + 3 new in util::smtsolver::cvc5lib)
```

Env vars the `cvc5-sys` build script reads (all set by the env file):

| var | value on dev machine | why |
|---|---|---|
| `CVC5_LIB_DIR` | `~/.cache/domino/cvc5-1.3.1-Linux-x86_64-static/lib` | skips cvc5-sys's build-from-source (no CMake needed); links `libcvc5.a` + `libcvc5parser.a` + `cadical`/`picpoly`/`picpolyxx`/`gmp` (all in that dir; the **non-GPL** release has exactly the set `cvc5-sys` links). |
| `CVC5_INCLUDE_DIR` | `…/include` | bindgen reads `cvc5/c/cvc5.h` + `cvc5_parser.h`. |
| `LIBCLANG_PATH` | `~/.cache/domino/libclang-18.1.1` | bindgen. The machine has **no** system libclang and no sudo; the script pulls the `libclang` PyPI wheel (just a `.so`). |
| `BINDGEN_EXTRA_CLANG_ARGS` | `-I/usr/lib/gcc/x86_64-linux-gnu/15/include` | the libclang wheel ships **no** builtin headers, so clang can't find `stddef.h`; point it at gcc's. A full clang/llvm install would not need this. |

Chose the **non-GPL** static release deliberately: the GPL one additionally links `cln`/`cocoa`/
`glpk`, which `cvc5-sys` 0.4.0's build script does not add → undefined symbols at link.

`cvc5-sys` 0.4.0's `[package.metadata.cvc5] version = "1.3.1"` is only checked on the
build-from-source path; with `CVC5_LIB_DIR` set it is ignored, so the 1.3.1 release is used to
match. 1.3.4 headers also worked in testing but 1.3.1 is the safe match.

## 5. Not done / follow-ups

- **`flake.nix` is untested.** No `nix` on the dev machine. `devShells.cvc5-lib` adds
  `pkgs.cmake` + `pkgs.llvmPackages.libclang` + `LIBCLANG_PATH`; the static cvc5 still comes from
  `scripts/setup-cvc5-lib.sh` (works anywhere with `curl` + `python3`). If someone wants a fully
  hermetic nix build, wire a `fetchzip` of the cvc5 release (hash TBD) and set `CVC5_LIB_DIR` from
  it — I did not, to avoid committing a hash I can't verify.
- **Disk on the dev machine is ~97% full.** The `cvc5-sys` static build + downloads are heavy
  (~300 MB target, ~200 MB cache). `rm -rf target/debug/incremental` reclaims ~2 GB when needed.
- `scripts/setup-cvc5-lib.sh` pins `CVC5_VERSION=1.3.1` / `LIBCLANG_WHEEL_VERSION=18.1.1`
  (overridable by env). Bump when cvc5-sys bumps its expected version.
- The `cvc5-lib` build is **not** in CI / `scripts/test-known-examples.sh` and should stay out
  until story 06 gives it a real consumer. `knownWorkingExamplesCheck` in `flake.nix` is untouched.

## 6. Acceptance criteria — status

- [x] `SmtSolver` has `push`/`pop`/`set_option`; `process::Communicator` implements them.
- [x] `cargo build --workspace` (no features) succeeds, does not pull in `cvc5` (verified: no
      `Compiling cvc5*` line).
- [x] `cargo build --workspace --features cvc5-lib` succeeds; prerequisites documented
      (`Readme.md`, `scripts/setup-cvc5-lib.sh`, this file).
- [x] `cargo test --workspace --features cvc5-lib` passes the push/pop test:
      `util::smtsolver::cvc5lib::test::push_pop_check_sat_and_model` (declare → sat → push →
      contradiction → unsat → pop → sat → `get_model` parses to `SmtModel`).
- [x] Transcript-order test: `…::transcript_receives_every_command_in_order` (checks
      `(set-logic ALL)`, `(declare-const …)`, `(check-sat)`, `(push 1)`, `(assert b)`,
      `(check-sat)`, `(pop 1)`, `(set-option :tlimit-per 1000)`, `(check-sat)` appear in order).
- [x] Bonus: `…::partial_writes_are_buffered_until_a_command_completes` guards the §3.1 workaround.
- [x] `scripts/test-known-examples.sh` code paths untouched; `domino prove` on
      `test-projects/test-loopunroll` still exits 0.
