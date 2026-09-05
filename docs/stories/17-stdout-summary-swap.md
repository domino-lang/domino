# Story 17 — Swap them: the concise report on stdout, the path tree in `summary.txt`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`render_tree`), story 09 (the incremental `flush`), story 12
(`render_summary` / `summary.txt`).
**Interacts with:** story 10 (`StopReason`, Ctrl-C), story 14 (parallel exploration must keep the
same two outputs).
**Blocks:** nothing.

---

## 1. Why this story exists

The two reports are on the wrong ends of the pipe.

`crates/domino/src/main.rs:220` prints **`render_tree(&run)`** (`driver.rs:1409`) to stdout: one
block per left path, every step of it, every right path under it with its verdict, plus the pruned
branches. On `kem-dem` `PKENC` that is a four-figure line count scrolling past — you cannot read
the verdict counts off it, and the terminal's scrollback is where it lives.

Meanwhile the report that actually answers "did it finish, and what did it find?" —
`render_summary` (`report.rs:113`): status, elapsed, path counts, verdict counts, the failing
pairs with their model files, the artifact list — is written to a **file** the user has to go and
open, and stdout only says `summary: <dir>/summary.txt` (`main.rs:221`).

### What the owner asked for

> I want that the stdout of debug command be what you write now in summary.txt but what it is
> logged there which is summary of paths and it is quite long, be written to summary.txt.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **stdout** | The concise report — today's `render_summary` output, unchanged in shape. |
| **`summary.txt`** | The full per-left-path tree — today's `render_tree` output. |
| **Filename** | Stays `summary.txt`, as asked. (`paths.txt` was considered and rejected: the owner named the file, and renaming would break every note and script that points at it.) |
| **Both, always** | Not an option to pick between: every run writes the file *and* prints the report. No new flag. |
| **Liveness** | `summary.txt` keeps being rewritten on every `flush` (once per left path), so an interrupted run still has the tree it got through. |
| **Exit codes** | Unchanged: `DebugNotVerified` when `!run.is_ok()`. |
| **Progress output** | Still stderr. Nothing about the bar/plain observer changes, except that it must be finished before the report prints. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 `render_tree` — `src/debug/driver.rs:1409`

Prints the header (`theorem …, proofstep N (L == R)`, `oracle …, claim …`), the `listing:` /
"line numbers are independent" note, then per left path its steps, its terminal, either
`[unsat: left path unreachable — pruned]` or the `right paths under #N:` block with one line per
right path and its verdict, then the `pruned under #N:` block. It is also used as an assertion
message in several driver tests (`:1775`, `:2078`, …) — keep it `pub` and keep its signature.

### 2.2 `render_summary` / `write_summary` — `src/debug/report.rs:72-235`

- `write_summary(run, elapsed, out_dir)` writes `render_summary(run, elapsed)` to `summary.txt`.
- `render_summary` blocks: header (theorem / games / oracle / claim / options), `status` +
  `elapsed`, `paths`, `verdicts`, `goal failures` (`write_pair_block`, capped at 20 + `… and N
  more`), `inconclusive`, `artifacts`. `chain_str` (`:98`) renders `L14 else → L36 return`,
  dropping `assert-holds` / `unwrap-some`.
- It is the **one** non-deterministic artifact: it carries the wall-clock `elapsed` line
  (`report.rs:66-71`). Every other file is byte-identical across two runs of an unchanged project.

### 2.3 The flush and the elapsed clock

`report::flush(run, elapsed, out_dir)` (`:44`) writes `trace.json`, `index.html` and
`summary.txt`; it is called after every left path (`driver.rs:813`) and once at the end (`:682`),
with `started.elapsed()` measured inside `run_debug_command` (`:466`). `main.rs` has no clock of
its own.

## 3. Work to do

### 3.1 Give `DebugRun` the elapsed time, skipped from the trace

```rust
/// Wall-clock time of the run so far. Updated before every `flush` and once
/// more at the end. `#[serde(skip)]` — `trace.json` and `index.html` stay
/// byte-deterministic (story 07), exactly like `out_dir`.
#[serde(skip)]
pub elapsed: Duration,
```

Set `run.elapsed = started.elapsed()` immediately before each `flush` call, and drop `flush`'s
and `write_summary`'s `elapsed` parameter — they read it off the run. This is what lets `main.rs`
print the concise report without threading a second clock through the CLI.

### 3.2 Swap the two sinks

In `src/debug/report.rs`:

- `write_summary(run, out_dir)` now writes **`driver::render_tree(run)`** to `summary.txt`.
  Rename the private helper to `render_paths_report` if that reads better, but keep the public
  function name `write_summary` and the path `summary.txt`.
- `render_summary(run, elapsed)` stays exactly as it is and becomes the function `main.rs` calls.
  Keep it `pub`.
- Add to `render_summary`'s `artifacts` block a line for the tree, and print the output directory
  once at the top of that block:

  ```text
  artifacts     _build/debug/kem_dem_cca_ssp/Game_A-Game_B/PKENC/same-output
    paths         summary.txt        (per-path tree: 128 left, 402 right)
    tree          index.html
    trace         trace.json
    listing       inlined.txt
    smt           smt/               (failures)
  ```

  `main.rs` then prints **nothing** but the report — delete the four `println!`s at
  `main.rs:221-229`; every pointer they carried is in the `artifacts` block already.

In `crates/domino/src/main.rs:220`:

```rust
print!("{}", sspverif::debug::report::render_summary(&run, run.elapsed));
```

Make sure the observer has finished (its `Finished` event clears the bar) before this prints, so
the report never lands inside a redrawn progress line.

### 3.3 Keep the tree honest for a partial run

`render_tree` says nothing today about *why* it ends where it does. Since it is now a file the
user reads after the fact, append one trailing line derived from `run.stop_reason` /
`run.admitted` (story 10/12 vocabulary, same wording as `render_summary`'s `status`):

```text
[STOPPED EARLY (interrupted by Ctrl-C) — 41 of 128 left paths explored]
```

and nothing at all for a completed run. Do not otherwise restyle the tree — the format was agreed
with the owner and story 16 leaves it alone too.

### 3.4 Tests

- `report.rs`'s story-12 tests (`summary_txt_completed_run_shape`,
  `summary_txt_stop_reason_status_lines`, `summary_txt_admitted_is_header_plus_status`,
  `summary_txt_differs_only_in_the_elapsed_line`, `summary_txt_goal_fail_ids_match_the_trace`,
  `:1269-1345`) are about the **concise report**: retarget them at `render_summary` and rename
  them `stdout_report_*`. `summary_txt_differs_only_in_the_elapsed_line` keeps its point — the
  concise report is a pure function of the run plus `elapsed`.
- Add `summary_txt_is_the_path_tree`: `write_summary` output for a fixture run equals
  `render_tree(&run)` (plus the stop-reason line), and contains one block per left path.
- `driver.rs:2351` / `:2402-2405` assert on `summary.txt` after an interrupted run — update them
  to expect the tree, and keep the assertion that the file exists and is non-empty.

## 4. Acceptance criteria

- [ ] `domino debug … | wc -l` on `kem-dem` `PKENC` is under ~40 lines regardless of how many
      paths were explored; today's number (four figures) goes in the implementation report.
- [ ] stdout is byte-identical to `summary.txt` from a pre-story-17 run of the same project,
      except for the `elapsed` line and the new `artifacts` header/`paths` row.
- [ ] `summary.txt` is byte-identical to what stdout printed before story 17, plus the trailing
      stop-reason line for a partial run and nothing for a complete one.
- [ ] A `Ctrl-C`ed run: stdout says `STOPPED EARLY (interrupted by Ctrl-C)`, `summary.txt` holds
      the tree of the left paths finished so far and ends with the bracketed stop line, and
      `trace.json` / `index.html` are unchanged in content by this story.
- [ ] An admitted claim prints the header plus `ADMITTED — nothing to check` on stdout and writes
      the two-line tree to `summary.txt`; no viewer/smt pointers are printed.
- [ ] Nothing but the report goes to stdout: progress output stays on stderr
      (`domino debug … 1>/dev/null` still shows the bar; `2>/dev/null` shows only the report).
- [ ] `trace.json` and `index.html` are still byte-identical across two runs of an unchanged
      project (proves `elapsed` really is `#[serde(skip)]`).
- [ ] Exit code is unchanged: 0 when `run.is_ok()`, the `DebugNotVerified` error otherwise, 130 on
      a second Ctrl-C.
- [ ] `cargo build`/`test`/`clippy --workspace` clean, and with `--features cvc5-lib`.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output | tee /tmp/out.txt
wc -l /tmp/out.txt $O/summary.txt          # short, long
$D debug … --oracle PKENC --claim same-output 2>/dev/null   # report only, no bar
$D debug … --oracle PKENC --claim same-output 1>/dev/null   # bar only, no report

# interrupted run
$D debug … --oracle PKENC --claim same-output   # Ctrl-C after a few paths
tail -3 $O/summary.txt                          # the bracketed stop line

# determinism of the deterministic pair
cp $O/trace.json /tmp/a.json && $D debug … --oracle PKENC --claim same-output && diff /tmp/a.json $O/trace.json
```

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release`.

## 6. Notes / risks

- **`summary.txt` now grows with the run.** It is rewritten in full on every `flush`, so a run
  with `n` left paths does `O(n²)` string work over the run. `trace.json` and `index.html` already
  do exactly that and are far larger, so this is not a new cost — but do not "optimise" it into an
  append-only writer: `flush` must stay idempotent and truncate-write, because a partial file has
  to be a *valid whole* file at every moment.
- **The name is now slightly off** — `summary.txt` holds the detailed tree. That is what the owner
  asked for; if it grates later, the rename is one constant and one line of docs, not a redesign.
- **Story 14 (parallel exploration)** will interleave left paths; the tree is ordered by left-path
  id, not completion order, and must stay that way. Whoever lands second reconciles.
- **Do not widen scope.** No `--quiet`, no `--format json`, no colour on stdout, no restyling of
  either report beyond the two additions named in §3.2 and §3.3.

## 7. State handed to the next story

Record in `docs/stories/17-…-IMPLEMENTATION-REPORT.md`: the new `DebugRun.elapsed` field and the
`flush` / `write_summary` signature change, the final `artifacts` block as implemented, the
before/after stdout line counts on `PKENC`, and the renamed tests.
