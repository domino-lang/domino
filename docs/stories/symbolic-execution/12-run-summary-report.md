# Story 12 — A concise run report file (`summary.txt`) and an explicit stop reason

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`src/debug/driver.rs`), story 09 (incremental flush), story 10
(unlimited `--max-paths`, `Ctrl-C` cancellation).
**Blocks:** nothing (story 14 extends the report with worker statistics).

---

## 1. Why this story exists

The only end-of-run summary today is the last paragraph of `render_tree` (`driver.rs:1249`),
printed to stdout after a full path-by-path dump that is thousands of lines long for `PKENC`. If
you piped the run to a file, scrolling back to find "did it finish, and what did it find?" is
work. And nothing anywhere says **why** a partial run stopped — `DebugRun.partial` is a bare
`bool` covering `--max-paths`, `Ctrl-C` and an executor cap alike.

### What the owner asked for

> I want a CLI concise debugging report written in a file, and it only gives a summary and whether
> all paths are explored or it is stopped earlier — including current statistics of the branches
> and paths explored, and how many verified, goal failures, unreachable and inconclusive there are.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **File** | `<out_dir>/summary.txt`, plain text, ~25 lines, written on **every** run — including a partial or interrupted one. |
| **Written when** | On every `report::flush` (i.e. after each left path) *and* at the end, so an interrupted run still has a current summary. |
| **Stop reason** | `DebugRun.partial: bool` is replaced by a `stop_reason: StopReason` enum serialised into `trace.json`. |
| **Wall-clock** | `summary.txt` **may** contain elapsed time; `trace.json` **may not** (story 07's byte-identical guarantee). `summary.txt` is explicitly excluded from that guarantee. |
| **stdout** | Unchanged — still exactly `render_tree` plus the `viewer:` line, with the `summary:` path added to the trailer. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 What is already computed (`src/debug/driver.rs`)

```rust
pub struct Summary {                                                    // :351
    pub left_paths, left_pruned, left_pruned_branches,
        right_paths, right_pruned_branches, sibling_shortcuts,
        verified, unreachable, goal_fails, inconclusive: usize,
}
```

`summarize(&run.left_paths, &run.left_pruned_branches)` (`:1220`) is pure, cheap and idempotent;
the driver already recomputes it after every left path (`explore_paths`, `:610`). `DebugRun`
(`:165`) also carries `theorem`, `proofstep`, `left_game`, `right_game`, `oracle`, `claim`,
`admitted`, `options: OptionsView` (`:223`), `left_paths`, `left_pruned_branches`, `partial`, and
`is_ok()` (`:372`, the exit-code criterion: `!partial && goal_fails == 0 && inconclusive == 0`).

`Verdict` (`:337`) is `Verified | Unreachable | GoalFails { model } | Inconclusive { model }`.
Failing pairs are therefore already enumerable from `run.left_paths[*].right_paths[*]`.

### 2.2 Where `partial` is set

Three places, all in `driver.rs`: the `on_left` closure and the `on_right` closure set
`run.partial = true` on the stop flag or on exceeding `opts.max_paths` (`explore_paths` `:610`,
`handle_left_path` `:748`), and (after story 10) the `ExecError::Cancelled` arms. Each of those
sites knows *which* reason applies.

### 2.3 Artifact writing

`src/debug/report.rs`: `write_trace_json` (`:22`), `flush` (`:40`), `write_html` (`:48`).
`flush` is called after every left path and once at the end of `run_debug_command`
(`driver.rs:566`). `inlined.txt` is written once at the end (`:562`).

### 2.4 Schema

`pub const TRACE_SCHEMA: u32` (`:162`) — **3** after story 10, **4** after story 11. Bump by one
from whatever you find, and say the number in the report.

## 3. Work to do

### 3.1 `StopReason` replaces `partial: bool` — `src/debug/driver.rs`

```rust
/// Why exploration ended. Serialised into `trace.json`; `summary.txt` prints the
/// human-readable form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum StopReason {
    /// Every path the pruner did not cut was explored.
    Completed,
    /// `--max-paths <n>` was reached.
    MaxPaths { limit: usize },
    /// `Ctrl-C`.
    Interrupted,
}

impl StopReason { pub fn is_partial(self) -> bool { !matches!(self, StopReason::Completed) } }
```

- `DebugRun.partial: bool` → `DebugRun.stop_reason: StopReason` (keep the field position so the
  serialised order stays predictable). Add `pub fn partial(&self) -> bool { self.stop_reason.is_partial() }`
  so `is_ok()`, `render_tree` and `index.html`'s `T.partial` need only a one-line change each
  (in the HTML: `const partial = T.stop_reason.kind !== "completed";`).
- Set it precisely at the three sites in §2.2 — `Interrupted` when the stop flag is set,
  `MaxPaths { limit }` when the cap fired, `Completed` (the initial value) otherwise.
- `DebugEvent::Finished { summary, partial }` (`progress.rs`) becomes
  `Finished { summary, stop_reason }`; `PlainObserver`'s final line prints
  `(stopped: interrupted)` / `(complete)`, and `BarObserver` is unchanged apart from the field.

### 3.2 `src/debug/report.rs` — `write_summary`

```rust
/// Write the concise run report to `<out_dir>/summary.txt`. Unlike
/// `trace.json` / `index.html` this file is NOT byte-deterministic — it carries
/// wall-clock elapsed time.
pub fn write_summary(run: &DebugRun, elapsed: Duration, out_dir: &Path) -> std::io::Result<PathBuf>;
```

and `flush(run, elapsed, out_dir)` calls it alongside the other two.

Exact shape (keep it stable — people will grep it):

```text
domino debug — summary
======================
theorem       kem_dem_cca_ssp, proofstep 0
games         Game_MON_CCA_PKE  ==  Game_MOD_CCA_PKE_Real_KEM
oracle        PKENC
claim         same-output
options       check-left=on check-right=on timeout=none max-paths=unlimited jobs=1 smt=failures

status        STOPPED EARLY (interrupted by Ctrl-C)     # or: COMPLETE — all paths explored
elapsed       1m 04s

paths
  left            4 explored of 6 syntactic   (1 unreachable, pruned at its terminal)
  right          71 explored                  (12 branches pruned)
  branches       3 left / 12 right pruned as unreachable
  pairs          71 checked

verdicts
  verified       57
  unreachable    12
  GOAL FAILS      1
  inconclusive    1

goal failures
  #3.7   L14 else → L36 return        models/3.7.smt2
inconclusive
  #4.2   L14 then → L31 abort         models/4.2.smt2

artifacts
  tree          index.html
  trace         trace.json
  listing       inlined.txt
  smt           smt/            (failures)
```

Rules:
- `status` is the first thing after the header block — it is the question the file exists to
  answer. Exactly one of `COMPLETE — all paths explored`,
  `STOPPED EARLY (interrupted by Ctrl-C)`, `STOPPED EARLY (--max-paths <n> reached)`, or
  `ADMITTED — nothing to check`.
- "left N explored of M syntactic" uses `ir::count_terminals` (story 10). If story 10 has not
  landed, drop the "of M" clause and note it in the report — do **not** implement counting here.
- The `goal failures` / `inconclusive` blocks list at most 20 entries each, then
  `… and N more (see index.html)`.
- Omit whole blocks that would be empty (no `goal failures` heading when there are none).
- No colour, no unicode box drawing beyond `=` and `→`.

### 3.3 Driver + CLI wiring

- `run_debug_command` takes `let started = Instant::now();` at the top and threads
  `started.elapsed()` into every `report::flush` call.
- After the tree, `main.rs` (`crates/domino/src/main.rs:136`) prints
  `summary: <out_dir>/summary.txt` next to the existing `viewer:` line.
- No new CLI flag: the file is always written. (It is ~1 KB.)

## 4. Acceptance criteria

- [ ] `summary.txt` exists after every non-admitted run, and after an admitted one it carries the
      header block plus `status ADMITTED — nothing to check`.
- [ ] A completed `PKGEN` run reports `COMPLETE — all paths explored`; a `--max-paths 20` run
      reports `STOPPED EARLY (--max-paths 20 reached)`; a `Ctrl-C`ed run reports
      `STOPPED EARLY (interrupted by Ctrl-C)`.
- [ ] Interrupting a run mid-way leaves a `summary.txt` whose counts match the `trace.json`
      written by the same flush (write a test that parses both and compares the four verdict
      counts and the path counts).
- [ ] The verdict counts in `summary.txt` equal `run.summary`, and the listed goal-fail ids equal
      the ids of the `goal-fails` pairs in `trace.json` (unit test over a synthetic `DebugRun`).
- [ ] `DebugRun.stop_reason` is in `trace.json`, `partial` is gone, `index.html` still shows its
      `PARTIAL — exploration stopped early` chip (now with the reason in its text), and
      `TRACE_SCHEMA` is bumped.
- [ ] `render_tree`'s stdout output is unchanged except that the `(PARTIAL: …)` line names the
      reason.
- [ ] `trace.json` / `index.html` stay byte-deterministic across two identical runs;
      `summary.txt` differs only in the `elapsed` line (assert exactly that in a test:
      diff the two files and require one differing line).
- [ ] `cargo build`/`test`/`clippy --workspace` and `--features cvc5-lib` all clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKGEN --claim same-output
cat $O/PKGEN/same-output/summary.txt

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output --max-paths 20
grep status $O/PKENC/same-output/summary.txt

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output   # Ctrl-C after ~10s
grep -A2 status $O/PKENC/same-output/summary.txt
```

Smaller smoke tests first: `test-projects/test-splitinvoke`, `example-projects/hello-world`.

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release`.

## 6. Notes / risks

- **Do not let time leak into `trace.json`.** `elapsed` is a parameter of `write_summary`, never a
  field of `DebugRun`. Story 07's determinism guarantee is load-bearing for several tests.
- **`summary.txt` is rewritten on every flush** (once per left path) — it is a kilobyte, so the
  cost is nil, and it is what makes an interrupted run informative.
- **`partial` → `stop_reason` touches the HTML.** The viewer reads `T.partial` in two places
  (the summary chip and the `PARTIAL` banner); update both and re-open the file to check.
- **Do not widen scope.** No JSON summary (that is `trace.json`), no per-oracle aggregation across
  runs, no exit-code changes.

## 7. State handed to the next story

Record in `docs/stories/12-…-IMPLEMENTATION-REPORT.md`: the final `summary.txt` template (paste a
real one for `PKENC`), the `StopReason` shape, the new `TRACE_SCHEMA`, the `flush` signature
change, and every call site that had to move from `run.partial` to `run.partial()`.
