# Story 10 — Implementation report: path totals, honest bars, unlimited `--max-paths`, responsive `Ctrl-C`

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** stories 05 (`exec.rs`), 06 (`driver.rs`), 08 (branch pruning), 09 (`progress.rs`).
**Blocks / feeds:** story 11 (`SmtWriter`), 12 (`StopReason` — replaces the `partial` bool),
13 (`goal_smt`), 14 (parallel exploration — reuses `Totals`, `ExecError::Cancelled`, and quotes
the measured totals below to size its worker pool).

Each of stories 10–13 bumps `TRACE_SCHEMA` by one. **This story took it from 2 → 3.** Whichever
of 11–13 lands next bumps 3 → 4.

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/ir.rs` | **new** `pub fn count_terminals(&InlinedOracle) -> u64` — solver-free syntactic terminal count (one recursive fold, saturating adds). |
| `src/debug/exec.rs` | **new** `ExecError::Cancelled` variant; new test `count_terminals_equals_unpruned_path_count`. |
| `src/debug/progress.rs` | **new** `DebugEvent::Totals { left_total, right_total }` (2nd variant, after `Started`); `PlainObserver` gained `left_total` / `right_total` fields + `plain_line` now takes them; `BarObserver` switched from two spinners to two bounded bars on `Totals`. |
| `src/debug/driver.rs` | `DebugOptions.max_paths` / `OptionsView.max_paths` → `Option<usize>` (default `None`); `TRACE_SCHEMA = 3`; both `--max-paths` cap checks use `is_some_and`; `SolverPruner` gained a `stop: Option<&AtomicBool>` field checked at the top of `enter` (returns `ExecError::Cancelled`); `explore_paths` / `handle_left_path` convert `Cancelled` → `run.partial = true` instead of propagating; `Totals` emitted once after `Started` (skipped for admitted). |
| `src/debug/report.rs` | viewer chip renders `max-paths: unlimited` when `null`; tests updated for schema 3 + a `null` `max_paths` case. |
| `crates/domino/src/cli.rs` | `Debug::max_paths: Option<usize>`, no `default_value_t`. |
| `crates/domino/src/main.rs` | `max_paths` passes straight through; `ctrlc` handler is now a **counter** — 1st press sets the flag + prints the interrupt notice, 2nd press `std::process::exit(130)`. |

Verdicts, paths and solver-call counts are unchanged. `count_terminals` is a pure function of the
IR; the totals live only in `DebugEvent`s and the bar — **not** in `DebugRun` / `trace.json`
(story 07 determinism, deliberately preserved — see §5).

## 2. `ir::count_terminals` — signature, location, semantics

```rust
// src/debug/ir.rs  (immediately after `inline_oracle`)
pub fn count_terminals(inlined: &InlinedOracle) -> u64
```

One private recursive helper `f(stmts: &[InlStmt], k_fall: u64, k_ret: u64) -> u64` over a
statement slice with two continuation counts, entered as `f(&inlined.body.0, 1, 1)`:

```text
[]                     -> k_fall
Assign | Sample :: r   -> f(r, k_fall, k_ret)
Unwrap          :: r   -> 1 + f(r, k_fall, k_ret)          // `none` aborts, `some` continues
Branch{t,e}     :: r   -> let k = f(r, k_fall, k_ret) in f(t, k, k_ret) + f(e, k, k_ret)
Call{body}      :: r   -> let k = f(r, k_fall, k_ret) in f(body, k, k)   // `return` resumes at r
Return          :: _   -> k_ret
Abort           :: _   -> 1
```

`saturating_add` throughout (only adds, so overflow is essentially impossible, but a pathological
composition can't hang or panic the UI). `loopunroll` has already run, so the IR is loop-free and
this is a finite fold.

**Acceptance test (`exec.rs::count_terminals_equals_unpruned_path_count`):** with no
`BranchOracle` the executor walks exactly the syntactic paths, so
`count_terminals(inl) == exec::execute(inl, gi, si, side, None).unwrap().len()` **exactly**.
Verified green for both game instances of:

- `test-projects/test-splitinvoke` (`game_split`, `game_tmp`), oracle `Query`
- `example-projects/hello-world` (`medium_composition`, `small_composition`), oracle `UsefulOracle`
- `example-projects/kem-dem/kem-dem-cca-ssp` (`Game_MON_CCA_PKE`, `Game_MOD_CCA_PKE_Real_KEM`),
  oracles `PKGEN`, `PKENC`, `PKDEC`

### Measured totals — `kem-dem` `kem_dem_cca_ssp`, proofstep 0 (story 14: size your pool from these)

`count_terminals` per side, i.e. `Totals { left_total, right_total }`:

| Oracle | `left_total` (`Game_MON_CCA_PKE`) | `right_total` (`Game_MOD_CCA_PKE_Real_KEM`) |
|---|---|---|
| `PKGEN` | 2 | 3 |
| `PKENC` | 6 | 16 |
| `PKDEC` | 5 | 13 |

These are **upper bounds**. With default pruning a full `PKENC` / `same-output` run actually
reaches **4** left paths (2 branch-pruned to `unwrap-none`) and **2** surviving right paths
(24 right branches pruned). The display always shows the reached tally next to the bound
(`4 left paths (2 pruned)`), never a bare `6/6`.

## 3. `DebugEvent` — variant list and emission order after this story

```rust
#[non_exhaustive]
pub enum DebugEvent<'a> {
    Started          { oracle: &'a str, claim: &'a str, admitted: bool },
    Totals           { left_total: u64, right_total: u64 },        // NEW (story 10)
    LeftPathStarted  { index: usize, id: &'a str },
    LeftPathPruned   { id: &'a str },
    PairChecked      { id: &'a str, verdict: &'a Verdict, elapsed: Duration },
    BranchPruned     { side: Side, id: &'a str, label: usize },
    LeftPathFinished { index: usize, running: Summary },
    Finished         { summary: Summary, partial: bool },
}
```

```text
Started
Totals                              // skipped for an admitted claim
  ( LeftPathStarted
      ( PairChecked | BranchPruned )*
      LeftPathPruned?
      LeftPathFinished )*
Finished
```

`Totals` is emitted from `run_debug_command` right after `Started` and **before** the observer is
wrapped in the `SharedObserver` `RefCell` / any solver work. Admitted claim: `Started { admitted:
true }` → `Finished`, still nothing between. Pinned by `driver.rs::observer_sees_a_well_formed_event_stream`
(`events[1] == "Totals"`, exactly one, `left_total`/`right_total` > 0, `left_total >= left_paths`).

## 4. `--max-paths` and `DebugOptions`

```rust
pub struct DebugOptions { …, pub max_paths: Option<usize> }   // Default → None
pub struct OptionsView  { …, pub max_paths: Option<usize> }   // null in trace.json when None
pub const TRACE_SCHEMA: u32 = 3;
```

- CLI: `--max-paths <N>` (no default). Omitted ⇒ `None` ⇒ unlimited; `Ctrl-C` is the stop.
- Cap checks: `if opts.max_paths.is_some_and(|m| *explored > m) { run.partial = true; break }`
  in both `explore_paths`'s `on_left` and `handle_left_path`'s `on_right` (unchanged logic
  otherwise).
- Verified end-to-end on `kem-dem` `PKENC` / `same-output`:
  - no flag → explores everything, `trace.json` `schema 3`, `options.max_paths` `null`,
    `partial false`, exit 0.
  - `--max-paths 3` → stops early, `partial true`, exit 1.

## 5. Determinism (unchanged from story 07/09)

- No field added to `DebugRun`. `count_terminals` output lives in `Totals` events + the bar only.
- `trace.json` for a `NopObserver` + `stop: None` + `max_paths: None` run differs from a
  pre-story-10 run **only** in `schema` (2 → 3) and `options.max_paths` (`1000` → `null`).
- `report.rs` determinism tests (`trace_json_round_trips_and_is_deterministic`,
  `html_is_byte_identical_across_runs`) still green; new `unlimited_max_paths_serialises_as_null`
  pins the `null`.
- The viewer reads `o.max_paths` defensively (`== null ? "unlimited" : …`), so a schema-2 and a
  schema-3 `trace.json` both open.

## 6. `Ctrl-C` that lands mid-sweep

Three moving parts:

1. **`ExecError::Cancelled`** (`exec.rs`). Not an error path — every driver call site converts it.
2. **`SolverPruner.stop: Option<&AtomicBool>`** (`driver.rs`). Checked at the very top of
   `enter`, before any `push` / `check_sat`, so it returns `Cancelled` **without opening a
   scope** — the `enter`/`leave` contract still holds, ancestor scopes get their `leave` during
   unwind, and `debug_assert_eq!(pruner.depth(), 0)` in `explore_paths` / `handle_left_path`
   still passes. This is what makes an interrupt land inside a branch-pruning sweep, not only at
   pair boundaries.
3. **Driver conversion.** `explore_paths` and `handle_left_path` `match` the
   `execute_streaming_with_oracle` result (captured *after* the closure block ends, so the
   `&mut DebugRun` reborrow is released): `Ok(())` → nothing, `Err(Cancelled)` → `run.partial =
   true`, `Err(e)` → `return Err(e.into())`. The partially-filled `LeftPath` is still pushed,
   `summarize` + `report::flush` still run, `render_tree` still prints the `(PARTIAL: …)` marker,
   and the process exits non-zero via `!run.is_ok()`.
4. **Second press** (`main.rs`): the `ctrlc` closure holds an `AtomicUsize`; press #1 sets the
   flag + prints `debug: interrupt — finishing the current solver query, then writing partial
   results (Ctrl-C again to abort now)`, press #2 calls `std::process::exit(130)`. A single
   in-flight cvc5 call is a blocking FFI call and is **not** cancellable — that is why press #2 is
   a hard exit, and `--timeout` bounds how long press #1 takes to land.

### Verified end-to-end

`kem-dem` `PKENC` / `same-output`, `SIGINT` sent the instant the first `debug: left 1/6` line
appeared:

- interrupt notice printed, exploration stopped **after left path #1** with its right subtree not
  yet explored — i.e. within one solver query,
- `trace.json` + `index.html` written, `"partial": true`, `"schema": 3`,
- stdout tree printed with `(PARTIAL: exploration stopped early — results are incomplete)`,
- exit code `1`.

### Measured `Ctrl-C` latency on `PKENC`

Bounded by a single terminal-pair `check-sat`. On this machine those run in **well under 100 ms**
without `--timeout` for `kem-dem` `PKENC`/`PKDEC` (the whole oracle explores in ~0.3–1 s of
solver time), so the practical first-press latency is *sub-100 ms*. With `--timeout <ms>` it is
bounded by `ms` per in-flight query. Unit tests `stop_flag_bails_with_a_partial_run` (pre-set
flag) and `stop_flag_set_mid_sweep_stops_cleanly` (flag flipped from the observer on the first
`PairChecked`) pin the mechanism and the stack-balance asserts.

## 7. Progress observers after this story

### `PlainObserver` (`--progress plain`, or `auto` when stderr is not a TTY)

- New line on `Totals`:
  `debug: 6 left paths, ≤16 right paths per left path (syntactic upper bounds)`
- `LeftPathStarted` / `PairChecked` carry `k/N` / `j/M` **once `Totals` has been seen**
  (`debug: left 3/6 (#3) …`, `debug:   #3.7/16  verified  0.01s`); before `Totals` (and in the
  unit tests that pass `0, 0`) they fall back to the exact pre-story-10 format.
- `plain_line` is now `fn plain_line(&DebugEvent, left_total: u64, right_total: u64) -> Option<String>`
  — still a pure function; `PlainObserver` threads the two `u64`s as fields set on `Totals`.

### `BarObserver` (`--progress bar`, or `auto` on a TTY)

Two spinners until `Totals`, then two **bounded** bars:

```text
left   ▕████░░░░░░░░░░░░░░░░░░░░▏ 3/6    #3
pairs  ▕████████████████████████▏ 16/16  ✓2 ·68 ✗1 ?0 ✂12  [0:00:38]
```

- `Totals`: `set_length(left_total.max(1))` / `(right_total.max(1))`, styles swapped
  spinner → bar, steady tick disabled.
- `LeftPathStarted { index }`: `left.set_position(index-1)`, `pairs.set_position(0)`, tally
  message re-rendered (run-wide `✓·✗?✂` counts, as story 09).
- `PairChecked`: `pairs.inc(1)` + a `clamp_len` guard (`set_length(pos)` if a `Prune`-free
  re-entry ever pushed `pos` past `len`).
- `BranchPruned` (any side): `✂` tally++. **Pruned-subtree crediting to the bar position was NOT
  done** (§3.6 stretch — see §8).
- `LeftPathFinished { index }`: `left.set_position(index)`, `pairs.set_position(pairs.length())`
  so a sweep that pruned its way to the end reads `16/16`, not stalled.
- `Finished`: `finish_and_clear()` both + `MultiProgress::clear()` (unchanged — stdout tree lands
  on a clean terminal).

## 8. §3.6 stretch — pruned-subtree crediting to the bar: **NOT DONE**

The `pairs` bar credits pruned right-side work only at `LeftPathFinished` (snap to full). Between
`LeftPathStarted` and `LeftPathFinished` a heavily-pruned sweep can sit at a low position and then
jump to `M/M`. Attributing the exact cut-subtree size would need a `subtree_terminals: u64` on
`BranchQuery`, computed in `Executor::descend` from the child block plus a bottom-up fold over the
live `frames` stack, and `pairs.inc(subtree_terminals)` on `BranchPruned`. Left for a follow-up;
`§3.6` of the story file has the sketch.

## 9. Build / test status

```
cargo build   --workspace                         # clean
cargo build   --workspace --features cvc5-lib      # clean (domino binary relinked)
cargo clippy  --workspace                          # clean
cargo clippy  --workspace --features cvc5-lib      # clean
cargo test    --workspace                          # 128 + 2 pass, 4 ignored (pre-existing)
cargo test    --workspace --features cvc5-lib      # 142 + 2 pass, 4 ignored (pre-existing)
```

`--features cvc5-lib` test-binary link is memory-heavy — use `CARGO_BUILD_JOBS=2 cargo test -j2`
(OOMs at full parallelism on this machine; noted in story 09's report too).

New / changed tests:
- `debug::exec::tests::count_terminals_equals_unpruned_path_count`
- `debug::progress::tests::plain_lines_are_terse_and_greppable` (extended: totals line, `k/N`)
- `debug::progress::tests::plain_observer_remembers_totals_across_events`
- `debug::report::tests::unlimited_max_paths_serialises_as_null`
- `debug::report::tests::trace_json_round_trips_and_is_deterministic` (schema 2 → 3)
- `debug::driver::tests::observer_sees_a_well_formed_event_stream` (pins `Totals`)
- `debug::driver::tests::stop_flag_set_mid_sweep_stops_cleanly` (new)
- `debug::driver::tests::max_paths_stops_early_and_flags_partial` (`Some(1)`)

## 10. Notes for follow-up

- Story 12 replaces `DebugRun.partial: bool` with a `StopReason` enum. The three sites that set
  `run.partial = true` today (`--max-paths` cap ×2, `Err(Cancelled)` ×2, pre-set-flag in
  `on_left`/`on_right`) are where `StopReason::{MaxPaths, Interrupted}` should be distinguished.
- `count_terminals` would be the natural source if a later story wants the totals *in*
  `trace.json` — but that must be a deliberate schema bump, not a drive-by.
- The `PlainObserver` `k/N` lines assume `Totals` arrives first; it always does for a
  non-admitted run. If a future story emits per-path lines for an admitted run, guard for
  `left_total == 0`.
