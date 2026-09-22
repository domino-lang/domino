# Story 17 — Implementation report: concise report on stdout, path tree in `summary.txt`

**Status:** done, uncommitted (per the owner's instruction — commit message at the bottom).
**Branch:** `amir/symbolic-execution-debugger`
**Builds/tests/clippy:** clean with and without `--features cvc5-lib`, incl. `--all-targets`.

---

## 1. What changed

The two reports were swapped end-for-end, exactly as §1 of the story asked:

| Sink | Before story 17 | After story 17 |
|---|---|---|
| **stdout** | `driver::render_tree` — the full per-left-path tree + 4 `println!` pointer lines | `report::render_summary` — the concise run report, nothing else |
| **`<out>/summary.txt`** | `report::render_summary` — the concise report (carried `elapsed`) | `driver::render_tree` + a trailing stop line for a partial run |

No new flag. Both are written on every run. `summary.txt` is still rewritten on every
`flush` (once per left path), so an interrupted run keeps the tree it got through.

## 2. Code changes

### 2.1 `DebugRun.elapsed` (`src/debug/driver.rs`)

New field, immediately after `out_dir`:

```rust
/// Wall-clock time of the run so far. Updated immediately before every
/// `report::flush` (once per left path) and once more at the end, so
/// `main.rs` can print the concise stdout report without threading its own
/// clock through the CLI. `#[serde(skip)]` — `trace.json` and `index.html`
/// stay byte-deterministic (story 07), exactly like `out_dir`. Only
/// `summary.txt`'s sibling on stdout (`render_summary`) reads it.
#[serde(skip)]
pub elapsed: Duration,
```

- Initialised to `Duration::ZERO` in the `DebugRun { … }` literal.
- `run.elapsed = started.elapsed();` is set on the line **before** each of the two
  `report::flush` calls in `driver.rs` (the per-left-path flush inside the `on_left`
  closure, and the final flush in `run_debug_command`).
- `started: Instant` is still threaded into `explore_paths` (it feeds `run.elapsed`).

### 2.2 `flush` / `write_summary` signature change (`src/debug/report.rs`)

```rust
pub fn flush(run: &DebugRun, out_dir: &Path) -> std::io::Result<()>        // was (run, elapsed, out_dir)
pub fn write_summary(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf>   // was (run, elapsed, out_dir)
```

- `write_summary` now writes `render_paths_report(run)` — a new private helper:
  `driver::render_tree(run)` plus, for a partial run, a blank line and one trailing
  bracketed line (`stop_line`, also new & private). Nothing appended for a completed
  or admitted run.
- `render_summary` kept its body verbatim except: it is now `pub`, takes only
  `run: &DebugRun` (reads `run.elapsed` into a local `elapsed`), and its `artifacts`
  block changed (below).
- `report.rs` now imports `driver::{self, …}` and dropped `use std::time::Duration`
  (only `format_elapsed` still needs `Duration`, referenced as `std::time::Duration`).

### 2.3 The `artifacts` block, as implemented

```text
artifacts     <out_dir>
  paths         summary.txt        (per-path tree: 4 left, 2 right)
  tree          index.html
  trace         trace.json
  listing       inlined.txt
  smt           smt/               (failures)
  transcript    transcript.smt2        (only with --transcript)
```

- Heading line carries `run.out_dir` (absolute; fine — `render_summary` output is not
  a determinism-guaranteed artifact, and `out_dir` is `#[serde(skip)]` so `trace.json`
  is unaffected).
- `paths` row is first; its counts are `summary.left_paths` / `summary.right_paths`.
- `smt` / `transcript` rows unchanged in condition, only re-indented to line up.
- For an admitted claim `render_summary` still returns after the `status` line — no
  `artifacts` block, no viewer/smt pointers (story acceptance §4).

### 2.4 The trailing stop line (`summary.txt`, partial runs only)

```text
[STOPPED EARLY (interrupted by Ctrl-C) — 4 of 6 left paths explored]
[STOPPED EARLY (--max-paths 20 reached) — 20 of 128 left paths explored]
```

Status wording is identical to `render_summary`'s `status` line. `N` is
`run.left_paths.len()`, `M` is `run.left_syntactic`. `render_tree`'s own
`(PARTIAL: … — results are incomplete)` summary line (added by story 10/12) is
**unchanged** — so `summary.txt` for a partial run is byte-identical to the old
stdout plus this one extra bracketed line, which is what acceptance §3 asks for.

### 2.5 `crates/domino/src/main.rs`

The 5 print statements (`render_tree` + 4 pointer `println!`s) collapse to:

```rust
print!("{}", sspverif::debug::report::render_summary(&run));
```

`render_tree` dropped from the `use`. The `Finished` event (which calls
`finish_and_clear()` on the bars) is fired inside `run_debug_command` before it
returns, so the report never lands in a redrawn progress line — no extra flush
needed in `main.rs`.

### 2.6 `crates/domino/src/cli.rs`

`--progress` doc: "stdout stays the final tree" → "stdout carries only the final
concise report".

## 3. Tests

### `src/debug/report.rs`

- The 5 story-12 `summary_txt_*` tests → renamed `stdout_report_*`, retargeted at
  `render_summary` via a new `stdout_report_of(run, elapsed)` helper (clones the run,
  sets `elapsed`, calls `render_summary`). `stdout_report_completed_run_shape` gained
  two asserts on the new `artifacts` header + `paths` row.
  `stdout_report_differs_only_in_the_elapsed_line` keeps its point unchanged.
- New `summary_txt_is_the_path_tree`: `write_summary` output for the fixture run
  equals `driver::render_tree(&run)` exactly (completed run), has one `left path #`
  block per left path, is not the concise report; a partial run ends with the
  bracketed stop line (both `Interrupted` and `MaxPaths` wording checked); an
  admitted run is the two-line tree with no stop line.
- New `summary_txt_is_byte_identical_across_runs` (replaces the implicit
  "summary.txt carries elapsed" contract): two writes of the same run are identical.
- `synthetic_run` gained `elapsed: Duration::ZERO`.

### `src/debug/driver.rs`

- `stop_flag_bails_with_a_partial_run` (`:~2383`): the `summary.txt` assertion now
  also reads the file and asserts it is non-empty.
- `stop_flag_set_mid_sweep_stops_cleanly` (`:~2436`): the story-12 block that
  grepped the concise report's `verified`/`GOAL FAILS`/`pairs` lines out of
  `summary.txt` now asserts `summary.txt` *starts with* `render_tree(&run)`, starts
  with `"theorem "`, ends with the `[STOPPED EARLY (interrupted by Ctrl-C) — N of M
  left paths explored]` line, has one `left path #` block per explored left path, and
  contains render_tree's `"{verified} verified, {unreachable} unreachable"` fragment.

All `debug::` tests pass (61 lib + 19 driver, with `--features cvc5-lib`).

## 4. Before/after line counts (kem-dem)

Acceptance §4 wanted "today's number (four figures)" for `render_tree` on PKENC.
**That expectation is stale** — stories 08 (branch pruning) and 15 (slimmer base
frame) already cut the PKENC tree far below four figures in the current branch:

| `domino debug … --oracle PKENC --claim same-output` | before story 17 (stdout) | after story 17 |
|---|---|---|
| stdout | 67 lines (the full tree) | **29 lines** (concise report) |
| `summary.txt` | ~24 lines (concise report) | 67 lines (the tree) |

stdout is a **fixed 29 lines** for every claim I tried (`same-output`, `invariant`,
`equal-aborts` on PKENC/PKDEC; the count only moves with the number of goal-fail /
inconclusive pairs listed). The largest tree I produced was PKENC `invariant` with
`--no-check-left --no-check-right` at **151** `summary.txt` lines. Acceptance's
"under ~40 lines regardless of paths explored" for stdout: **met (29)**.

Other acceptance checks verified by hand on `kem-dem-cca-ssp` proofstep 0:

- `2>/dev/null` → report only, no bar. `1>/dev/null` → progress only (stderr).
- `trace.json` byte-identical across two runs (`elapsed` never appears in it —
  `#[serde(skip)]` confirmed).
- Admitted claim (`lemma-kem-correctness`): stdout is header + `status ADMITTED —
  nothing to check` + `elapsed`, no `artifacts`; `summary.txt` is the two-line
  "claim is admitted — nothing to check." tree.
- Exit code unchanged: `0` on `run.is_ok()`, `DebugNotVerified` otherwise.

## 5. State handed to the next story (story 14, parallel exploration — goes last)

- **`DebugRun` has a new field `elapsed: Duration`, `#[serde(skip)]`**, positioned
  right after `out_dir`. Set it (`run.elapsed = started.elapsed()`) before any
  `report::flush` you add. It does **not** enter `trace.json` / `index.html`.
- **`report::flush(run, out_dir)` and `report::write_summary(run, out_dir)` lost
  their `elapsed` parameter.** Story 14 must keep calling `flush` per completed left
  path; the tree in `summary.txt` is still ordered by left-path id (`run.left_paths`
  order), not completion order — whoever interleaves left paths must insert into
  `run.left_paths` in id order so `render_tree` / `render_paths_report` stay stable.
- **`report::render_summary(run) -> String` is now `pub`** and is what `main.rs`
  prints. It must stay a pure function of `run` + `run.elapsed`. The `options` line
  still hardcodes `jobs=1` (`report.rs`, in the header block) — **story 14 changes
  that string** to the real job count and should update
  `stdout_report_completed_run_shape`'s assertion on it.
- **`summary.txt` is now byte-deterministic** across two runs of an unchanged project
  (no `elapsed`), except that `render_tree`'s `listing: <out_dir>/inlined.txt` line
  embeds the absolute out dir — deterministic for a given project, not across
  different `--out` paths. If story 14 ever needs summary.txt path-independent, that
  one `render_tree` line is the only obstacle.
- `render_tree`'s trailing stop line for `summary.txt` is added by
  `report::render_paths_report` (private), not by `render_tree` itself — `render_tree`
  is unchanged and still safe to use as a test assertion message.
- The `TRACE_SCHEMA` was **not** bumped: no serialised shape changed (`elapsed` is
  skipped). Still `7`.
