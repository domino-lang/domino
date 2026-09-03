# Story 10 — Path totals, honest progress bars, unlimited `--max-paths`, responsive `Ctrl-C`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 05 (`src/debug/exec.rs`), story 06 (`src/debug/driver.rs`), story 08
(branch pruning), story 09 (`src/debug/progress.rs`).
**Blocks:** story 12 (stop reasons), story 14 (parallel exploration reuses the totals events).

---

## 1. Why this story exists

Story 09 gave `domino debug` live progress, but the two `indicatif` lines are **spinners with a
running counter**, not progress bars — story 08 made both sides stream, so the driver has no
up-front totals and the display can only say "71 pairs so far", never "71 of 96".

### What the owner asked for

> Now that we have live progress for debug command, I want to know how many left paths exist in
> total and how many of them have been explored so far. Also, I want another progress bar that
> tells me how many right paths exist for each left path and how many of them have been explored.
> This could be two progress bars. One for left and one for right that resets when left goes to a
> new path. I want the max-path limit to be unlimited by default. The `Ctrl-C` should help stop
> the exploration.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Where totals come from** | A **solver-free, purely syntactic** path count over the inlined IR (`InlBlock`), computed once per side immediately after `inline_oracle`. No extra execution pass, no solver calls. |
| **What the total means** | An **upper bound**: the number of syntactic terminals. Branch pruning (story 08) and `--check-left` mean the run reaches fewer. The UI says `k/N` and shows the pruned tally next to it; it never claims the total is exact. |
| **Right total** | The right oracle's syntactic terminal count. It is the **same number for every left path** (same oracle, same IR) — the bar length is constant, only the position resets. |
| **`--max-paths`** | `Option<usize>`, **unlimited by default**. `--max-paths <N>` opts back in. |
| **`Ctrl-C`** | Must take effect while the driver is inside a branch-pruning sweep too, not only at path boundaries. A **second** `Ctrl-C` exits the process immediately. |
| **Verdicts** | Unchanged. Observability + limits only: same paths, same solver calls, same verdicts. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The inlined IR — `src/debug/ir.rs`

```rust
pub struct InlinedOracle { …, pub body: InlBlock, pub listing: Listing }   // :74
pub struct InlBlock(pub Vec<InlStmt>);                                     // :88
pub enum InlStmt {                                                          // :91
    Assign { label, target, rhs },
    Sample { label, target, sample_id, ty, sample_name },
    Unwrap { label, target, inner },          // forks: `some` continues, `none` aborts
    Branch { label, cond, then: InlBlock, els: InlBlock, is_assert },
    Call   { label, frame, bind, body: InlBlock },   // callee body NESTED, not flattened
    Return { label, value },                  // terminal at the entry frame; resumes the
                                              // caller inside a `Call` frame
    Abort  { label },                         // always a global terminal
}
```

`loopunroll` has already run, so there are no loops: the terminal count is a finite,
purely structural property of this tree.

### 2.2 The executor — `src/debug/exec.rs` (stories 05 / 08)

- `execute_streaming_with_oracle(inlined, game_inst, sample_info, side, max_paths, oracle, on_path)`
  (`:1151`) walks the IR depth-first. `Executor::walk` (`:614`) keeps a `Vec<Cursor>` frame stack;
  `Executor::descend` (`:846`) is the single choke point through which **every** fork passes — it
  asks the `BranchOracle` (`:209`) and calls `leave` on every exit path.
- `BranchQuery` (`:178`) carries `label`, `decision`, `steps`, the new `decls` / `constraints`
  since the last scope, and `sibling: 0|1`.
- `ExecError` (`:215`) has `OracleNotExported` and `MaxPathsExceeded`.
- The driver passes `max_paths: None` into the executor today — `opts.max_paths` is enforced by
  the driver's own counters, never by the executor.

### 2.3 The driver — `src/debug/driver.rs` (stories 06 / 08 / 09)

- `DebugOptions { check_left, check_right, timeout_ms, max_paths: usize }` (`:85`), default
  `max_paths: 1000` (`:102`).
- `OptionsView` (`:223`) is the serialised mirror of it inside `DebugRun` → **`trace.json` schema
  changes when `max_paths` changes type.** `pub const TRACE_SCHEMA: u32 = 2;` (`:162`).
- `run_debug_command(…, observer: &mut dyn DebugObserver, stop: Option<&AtomicBool>)` (`:386`).
- `explore_paths` (`:610`) creates the left `SolverPruner`, runs the left side streaming, and in
  its `on_left` closure checks the stop flag, bumps `explored`, compares against `opts.max_paths`,
  calls `handle_left_path` (`:748`), pushes the `LeftPath`, re-`summarize`s and `report::flush`es.
- `handle_left_path`'s `on_right` closure does the same for right terminals, calling
  `handle_right_path` (`:881`) → `check_pair` (`:920`).
- `SolverPruner` (`:980`) is the `BranchOracle`: `push` + write-delta on `enter`, `pop` on
  `leave`, `Prune` only on `unsat`. **The stop flag is not checked anywhere inside it** — that is
  the `Ctrl-C` latency bug this story fixes.

### 2.4 Progress — `src/debug/progress.rs` (story 09)

`DebugEvent` (`#[non_exhaustive]`, `:57`) with `Started`, `LeftPathStarted { index, id }`,
`LeftPathPruned`, `PairChecked { id, verdict, elapsed }`, `BranchPruned { side, id, label }`,
`LeftPathFinished { index, running }`, `Finished { summary, partial }`; `DebugObserver`;
`SharedObserver = RefCell<&mut dyn DebugObserver>`; `NopObserver`; `PlainObserver` (one stderr
line per event, via the testable `plain_line`); `BarObserver` (`MultiProgress` + two
`ProgressBar::new_spinner()`s + a `Tally`).

### 2.5 CLI — `crates/domino/src/cli.rs` / `main.rs`

`struct Debug` (`cli.rs:63`) has `…, max_paths: usize` with `default_value_t = 1000` (`:95`) and
`progress: ProgressMode` (`:100`). `fn debug` (`main.rs:136`) builds `DebugOptions`, the observer,
installs a `ctrlc::try_set_handler` that stores `true` into an `AtomicBool`, and passes
`Some(&stop)`.

## 3. Work to do

### 3.1 `src/debug/ir.rs` — syntactic path counting (new, solver-free)

```rust
/// Number of syntactic terminals (`return` at the entry frame, `abort`, and the
/// implicit abort of every `unwrap`) reachable through this oracle's IR.
///
/// Purely structural: it is an **upper bound** on the paths a run explores,
/// because the solver prunes infeasible branches. Saturating — a pathological
/// oracle cannot make this overflow or hang the UI.
pub fn count_terminals(inlined: &InlinedOracle) -> u64;
```

Implementation is one recursive helper over a statement slice with two continuation counts:

```text
f(stmts, k_fall, k_ret) =
  []                       -> k_fall
  Assign|Sample  :: rest   -> f(rest, k_fall, k_ret)
  Unwrap         :: rest   -> 1 + f(rest, k_fall, k_ret)        // `none` aborts, `some` continues
  Branch{t,e}    :: rest   -> let k = f(rest, k_fall, k_ret) in f(t, k, k_ret) + f(e, k, k_ret)
  Call{body}     :: rest   -> let k = f(rest, k_fall, k_ret) in f(body, k, k)   // return resumes here
  Return         :: _      -> k_ret
  Abort          :: _      -> 1
```

Entry: `f(inlined.body.0, 1, 1)`. All arithmetic `saturating_add` / `saturating_mul`-free (only
adds). Unit-test it against `execute(...).len()` on `test-projects/test-splitinvoke`,
`example-projects/hello-world` and both sides of `kem-dem` `PKENC` — with no `BranchOracle` the
executor explores exactly the syntactic paths, so **`count_terminals == execute(..).len()`
exactly**. That equality is the acceptance test; it is what makes the number trustworthy.

### 3.2 `src/debug/progress.rs` — one new event

```rust
    /// Syntactic terminal counts for both sides, from `ir::count_terminals`.
    /// Emitted once, after inlining and before any solver work. Both are upper
    /// bounds: branch pruning and `--check-left` cut the real numbers down.
    /// `right_total` is per left path (the right oracle is the same under each).
    Totals { left_total: u64, right_total: u64 },
```

Add it after `Started` in the documented event order in the module docs.

- `PlainObserver`: `debug: 6 left paths, ≤12 right paths per left path (syntactic upper bounds)`.
- `BarObserver`: replace both spinners with real bars.

### 3.3 `BarObserver` — two real bars

```text
left   ▕████████░░░░░░░░▏ 3/6    PKENC / same-output
pairs  ▕██████████████░░▏ 71/96  ✓2 ·68 ✗1 ?0 ✂12   [0:00:38]
```

- On `Totals`: `left.set_length(left_total)`, `pairs.set_length(right_total)`, switch both styles
  from `new_spinner()` to a bar template (`{bar:24} {pos}/{len} {msg}`); keep the elapsed timer on
  the pairs line. Guard against `len == 0`.
- `LeftPathStarted { index, .. }`: `left.set_position(index - 1)`; `pairs.set_position(0)`;
  reset the *per-left-path* part of the tally message. Keep the run-wide tally too — render
  `✓2 ·68 ✗1 ?0 ✂12` from the running totals, as today.
- `PairChecked`: `pairs.inc(1)`.
- `BranchPruned { side: Right, .. }`: bump the `✂` tally. Do **not** try to advance the bar by the
  size of the cut subtree (see §3.6).
- `LeftPathFinished { index, .. }`: `left.set_position(index)`, and
  `pairs.set_position(pairs.length())` so a sweep that pruned its way to the end reads as complete
  rather than stalling at 60 %.
- `Finished`: as today — finish and clear both bars, then `MultiProgress::clear()` so `main.rs`
  prints the tree onto a clean terminal.
- If the run somehow exceeds a length (it must not, but a `Prune`-free re-entry would),
  `indicatif` clamps; call `set_length(pos)` in that case rather than letting the bar look stuck.

`PlainObserver` gains the totals in its `LeftPathStarted` / `PairChecked` lines:
`debug: left 3/6 (#3) …` and `debug:   #3.7/12  verified  0.24s`. Keep every line one line, no
colour. `plain_line` stays a pure function of `(event, remembered totals)` — thread the totals
through `PlainObserver` as two `u64` fields set on `Totals`, and extend the existing
`plain_lines_are_terse_and_greppable` unit test.

### 3.4 `--max-paths` unlimited by default

- `DebugOptions.max_paths: Option<usize>` (`driver.rs:85`), `Default` → `None` (`:102`).
- `OptionsView.max_paths: Option<usize>` (`:223`); **bump `TRACE_SCHEMA` to `3`** (`:162`).
- Both cap checks (`explore_paths`'s `on_left`, `handle_left_path`'s `on_right`) become
  `if opts.max_paths.is_some_and(|m| *explored > m) { run.partial = true; … }`.
- `cli.rs`: `#[clap(long)] pub(crate) max_paths: Option<usize>,` — no `default_value_t`. Doc
  comment: *"Stop after this many explored paths (left paths + right paths). Unlimited by
  default."*
- Every existing `driver.rs` test that relied on the 1000 default keeps working; the one test (if
  any) that asserts on `options.max_paths` in `trace.json` is updated to `null`.

### 3.5 `Ctrl-C` that actually stops

Three changes:

1. **New `ExecError::Cancelled`** (`exec.rs:215`):
   ```rust
   #[error("exploration cancelled")]
   Cancelled,
   ```
2. **`SolverPruner` checks the flag.** Give it a `stop: Option<&AtomicBool>` field
   (`driver.rs:980`) and, at the top of `enter`, return `Err(ExecError::Cancelled)` when the flag
   is set. The `BranchOracle` contract guarantees `leave` runs for every successful `enter`, so
   the solver stack still unwinds balanced; the `debug_assert_eq!(pruner.depth(), 0)` assertions
   in `explore_paths` / `handle_left_path` must still hold (verify with a test that pre-sets the
   flag mid-sweep).
3. **The driver treats `Cancelled` as "stop", not "fail".** Where `explore_paths` and
   `handle_left_path` today do `execute_streaming_with_oracle(…)?`, match instead:
   ```rust
   match execute_streaming_with_oracle(…) {
       Ok(()) => {}
       Err(ExecError::Cancelled) => { run.partial = true; }
       Err(e) => return Err(e.into()),
   }
   ```
   Everything downstream is unchanged: the partially-filled `LeftPath` is pushed, `summarize`
   runs, `report::flush` writes `trace.json` / `index.html`, `render_tree` prints its
   `(PARTIAL: …)` marker and the process exits non-zero via `is_ok()`.

4. **Second `Ctrl-C` = immediate exit** (`crates/domino/src/main.rs:136`). Replace the one-shot
   handler with a counter:
   ```rust
   let hits = Arc::new(AtomicUsize::new(0));
   let _ = ctrlc::try_set_handler(move || {
       if hits.fetch_add(1, Ordering::Relaxed) == 0 {
           stop.store(true, Ordering::Relaxed);
           eprintln!("\ndebug: interrupt — finishing the current solver query, \
                      then writing partial results (Ctrl-C again to abort now)");
       } else {
           std::process::exit(130);
       }
   });
   ```
   Note in the module docs that a single in-flight cvc5 call is **not** cancellable (the
   `cvc5-lib` backend is a blocking FFI call), which is exactly why the second press is a hard
   exit. `--timeout` bounds how long the first press takes to land.

### 3.6 Explicit non-goal: crediting pruned subtrees to the bar

When story 08 prunes a fork, the bar does not know how many syntactic terminals were cut, so it
can sit at 60 % until `LeftPathFinished` jumps it to 100 %. Attributing the exact subtree size
would mean computing the continuation counts of the executor's live frame stack and threading a
`subtree_terminals` field through `BranchQuery`.

**Do not do this as part of the main body of work.** If §3.1–§3.5 are complete, green and
committed, and you have session budget left, it is a legitimate stretch (add
`subtree_terminals: u64` to `BranchQuery`, computed in `Executor::descend` from the child block
plus a bottom-up fold over `frames` — `k_fall_i = c_{i-1}`, `k_ret_i = c_{i-1}` for a `Call`
frame and `k_ret_{i-1}` for a `Sub` frame — and `pairs.inc(subtree_terminals)` on `BranchPruned`).
Otherwise just record in the implementation report that the bar credits pruned work only at the
end of each sweep.

## 4. Acceptance criteria

- [ ] `ir::count_terminals(&InlinedOracle) -> u64`, unit-tested to be **exactly equal** to
      `exec::execute(…).len()` for both sides of: `test-projects/test-splitinvoke`,
      `example-projects/hello-world`, and `kem-dem` `PKGEN` / `PKDEC` / `PKENC`.
- [ ] `DebugEvent::Totals { left_total, right_total }` is emitted once, after `Started` and before
      any solver call, and the mock-observer sequence test from story 09 is extended to pin it.
- [ ] `--progress bar` shows two **bounded** bars: `left k/N`, `pairs j/M`, the pairs bar resetting
      to `0/M` at every `LeftPathStarted` and reading `M/M` at `LeftPathFinished`.
- [ ] `--progress plain` prints the totals line and carries `k/N` / `j/M` in its per-path lines.
- [ ] `--max-paths` is unlimited by default: `domino debug … --oracle PKENC --claim same-output`
      with no flag explores every path and reports `partial: false`; `--max-paths 20` still stops
      early with `partial: true`. `OptionsView.max_paths` is `null` in `trace.json` for the former.
- [ ] `TRACE_SCHEMA == 3` and the viewer still opens both a schema-2 and a schema-3 `trace.json`
      (the HTML only reads fields it knows).
- [ ] A single `Ctrl-C` during a `PKENC` run stops within one solver query, prints the interrupt
      notice, writes `trace.json` + `index.html` with `"partial": true`, prints the tree with the
      `(PARTIAL: …)` marker, and exits non-zero. A second `Ctrl-C` exits immediately with 130.
- [ ] Unit test: `SolverPruner` with a pre-set stop flag returns `ExecError::Cancelled` from
      `enter`, the driver converts it to `partial = true` (not an `Err`), and the solver-stack
      balance `debug_assert`s hold.
- [ ] With `NopObserver` + `stop: None` + `max_paths: None`, `trace.json` for `PKENC` /
      `same-output` is identical to a pre-story-10 run except for `schema` and
      `options.max_paths`.
- [ ] `cargo build --workspace` / `--features cvc5-lib`, `cargo test --workspace` /
      `--features cvc5-lib`, `cargo clippy --workspace` / `--features cvc5-lib` all clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh          # from scripts/setup-cvc5-lib.sh
cargo build --workspace --features cvc5-lib

cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output   # two bars
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output \
   --progress plain 2>progress.log; head -3 progress.log       # totals line present

# unlimited by default
python3 -c 'import json;d=json.load(open("_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output/trace.json"));print(d["schema"], d["options"]["max_paths"], d["partial"])'

# interrupt: press Ctrl-C once ~10s in, then inspect
$D debug … --oracle PKENC --claim same-output ; echo "exit=$?"
```

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`,
`example-projects/simple-KEM-example`.

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`
> (`example-projects/known-good-slow.txt`). See `docs/stories/00-overview.md` §7.
> Build with `cargo build --workspace` — a bare `cargo build --release` does not relink the
> `domino` binary.

## 6. Notes / risks

- **The total is an upper bound and must be labelled as one.** Never print `6/6 left paths` when
  three were pruned as unreachable — print `3/6 (3 pruned)`. A number that silently lies is worse
  than a spinner.
- **Determinism.** `count_terminals` is a pure function of the IR; totals live in events and in
  the bar, never in `DebugRun`. Do not add them to `trace.json` "while you're here" — if a later
  story wants them there, it bumps the schema deliberately.
- **`ExecError::Cancelled` is not an error path.** Every driver call site must convert it. Missing
  one means a `Ctrl-C` throws away the run — exactly the bug story 09 fixed.
- **Do not widen scope.** No per-pair time estimates / ETA, no `--first-failure`, no changes to
  which paths are explored.

## 7. State handed to the next story

Record in `docs/stories/10-…-IMPLEMENTATION-REPORT.md`:

- The final `count_terminals` signature and where it lives, plus the measured totals for
  `kem-dem` `PKGEN` / `PKDEC` / `PKENC` (both sides) — story 14 quotes them when sizing its
  worker pool.
- The `DebugEvent` variant list and emission order after this story (story 14 extends it again).
- The new `DebugOptions.max_paths: Option<usize>` shape and `TRACE_SCHEMA = 3`.
- Measured `Ctrl-C` latency on `PKENC` with and without `--timeout`.
- Whether the §3.6 stretch (pruned-subtree crediting) was done.
