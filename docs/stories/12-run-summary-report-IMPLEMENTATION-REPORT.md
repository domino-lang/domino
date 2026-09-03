# Story 12 — Implementation report: `summary.txt` + explicit `StopReason`

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** stories 06 (`src/debug/driver.rs`), 09 (incremental flush), 10
(`count_terminals`, `Ctrl-C` cancellation, unlimited `--max-paths`), 11 (`SmtOut`, `flush`).
**Blocks / feeds:** story 14 (reuses `StopReason`; `flush` / `run_debug_command` signatures
changed — see §7). Story 13 (the viewer's `partial` → `stop_reason` migration is **already done**
here — see §5).

`TRACE_SCHEMA` went **4 → 5.** Whichever of 13 / 14 lands next bumps 5 → 6.

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/driver.rs` | New `pub enum StopReason { Completed, MaxPaths { limit: usize }, Interrupted }` (`#[serde(tag = "kind", rename_all = "kebab-case")]`), with `is_partial()` and `phrase()`. `DebugRun.partial: bool` → **removed**; replaced at the same field position by `stop_reason: StopReason`, preceded by a new `left_syntactic: u64`. `DebugRun::partial(&self) -> bool` accessor added (delegates to `stop_reason.is_partial()`). `is_ok()` now calls `self.partial()`. The five `run.partial = true` sites set `StopReason::Interrupted` (stop-flag + `ExecError::Cancelled`) or `StopReason::MaxPaths { limit }` (the `--max-paths` checks, restructured from `is_some_and` to `if let Some(m)` to capture the limit). `run_debug_command` opens with `let started = Instant::now();`; `explore_paths` gained a `started: Instant` param; both `report::flush` calls pass `started.elapsed()`. `DebugEvent::Finished` field `partial` → `stop_reason`. `render_tree`'s trailer line is now `(PARTIAL: <phrase> — results are incomplete)`. |
| `src/debug/report.rs` | New `pub fn write_summary(run, elapsed: Duration, out_dir) -> io::Result<PathBuf>` + private `render_summary`, `format_elapsed`, `chain_str`, `write_pair_block`. `flush` signature is now `flush(run, elapsed: Duration, out_dir)` and calls `write_summary` alongside the other two. Viewer template: the single `if (T.partial)` chip site now reads `T.stop_reason` (kebab `kind`), falls back to `T.partial`, and appends the reason to the chip text. Test fixture `synthetic_run` carries `left_syntactic` + `stop_reason`; schema asserts 4 → 5; five new `summary_txt_*` tests. |
| `src/debug/smtout.rs` | `SmtOut::as_str(self) -> &'static str` (kebab, matches `Serialize`) — used by `render_summary`'s `options` line and available to the CLI trailer. |
| `src/debug/progress.rs` | `DebugEvent::Finished { summary, stop_reason }`. `plain_line`'s final line ends `(complete)` / `(stopped: interrupted)` / `(stopped: max-paths N)` instead of `(partial: yes/no)`. `BarObserver` unchanged (`Finished { .. }`). Tests updated. |
| `crates/domino/src/main.rs` | Prints `summary: <out_dir>/summary.txt` after the tree, **unconditionally** (the file is written for admitted runs too); the `viewer:` line lost its leading blank line since `summary:` now carries it. |
| `docs/stories/13-…md`, `docs/stories/14-…md` | "Inherited" notes updated (schema is 5; `partial` is gone; viewer migration done; `flush` takes `elapsed`). |

Verdicts, path counts, solver-call counts, pruning and stdout tree are all unchanged. This story
only adds a file and renames one bool to an enum.

## 2. `summary.txt` — the template (real output)

`kem-dem/kem-dem-cca-ssp`, proofstep 0, `PKENC` / `same-output`, default flags, completed:

```text
domino debug — summary
======================
theorem       kem_dem_cca_ssp, proofstep 0
games         Game_MON_CCA_PKE  ==  Game_MOD_CCA_PKE_Real_KEM
oracle        PKENC
claim         same-output
options       check-left=on check-right=on timeout=none max-paths=unlimited jobs=1 smt=failures

status        COMPLETE — all paths explored
elapsed       1.0s

paths
  left         4 explored of 6 syntactic   (2 unreachable, pruned at its terminal)
  right        2 explored   (22 branches pruned)
  branches     2 left / 22 right pruned as unreachable
  pairs        2 checked

verdicts
  verified      2
  unreachable   0
  GOAL FAILS    0
  inconclusive  0

artifacts
  tree          index.html
  trace         trace.json
  listing       inlined.txt
  smt           smt/            (failures)
```

`--max-paths 3` on the same run:

```text
options       check-left=on check-right=on timeout=none max-paths=3 jobs=1 smt=failures

status        STOPPED EARLY (--max-paths 3 reached)
elapsed       0.9s

paths
  left         2 explored of 6 syntactic
  right        1 explored   (15 branches pruned)
  branches     2 left / 15 right pruned as unreachable
  pairs        1 checked
```

Admitted claim (`lemma-kem-correctness`) — header block + `status` + `elapsed`, nothing else:

```text
domino debug — summary
======================
theorem       kem_dem_cca_ssp, proofstep 0
games         Game_MON_CCA_PKE  ==  Game_MOD_CCA_PKE_Real_KEM
oracle        PKENC
claim         lemma-kem-correctness
options       check-left=on check-right=on timeout=none max-paths=unlimited jobs=1 smt=failures

status        ADMITTED — nothing to check
elapsed       0.6s
```

`goal failures` / `inconclusive` blocks (from a run with `theorem/invariant.smt2` deliberately
weakened, restored afterwards):

```text
goal failures
  #1.1    L23 else → L45 then → L65 return          models/1.1.smt2
  #2.1    L23 else → L45 else → L65 return          models/2.1.smt2
```

### Format rules (as implemented)

- Left column of the header block is `{:<14}` (label + padding, no separator). Sub-blocks indent
  two spaces then `{:<13}` (paths) / `{:<14}` (verdicts).
- `status` is exactly one of `COMPLETE — all paths explored`,
  `STOPPED EARLY (interrupted by Ctrl-C)`, `STOPPED EARLY (--max-paths <n> reached)`,
  `ADMITTED — nothing to check`.
- `elapsed`: `<h>h <mm>m <ss>s` / `<m>m <ss>s` / `<s.d>s`.
- `paths.left`: `<n> explored[ of <N> syntactic][   (<k> unreachable, pruned at its terminal)]`.
  The `of N` clause is present whenever `left_syntactic > 0` (i.e. any non-admitted run).
- `paths.right` / `paths.branches` parentheticals are dropped when their count is 0; the
  `branches` and `pairs` lines are always present.
- `chain_str` drops `assert-holds` / `unwrap-some` steps (the non-events) — only `then` / `else`
  / `assert-fails` / `unwrap-none` decisions plus the terminal (`return` / `abort`) are shown,
  joined by ` → `.
- `goal failures` / `inconclusive` blocks: omitted entirely when empty; at most 20 entries, then
  `  … and <n> more (see index.html)`.
- `artifacts.smt` line omitted when `--smt none`; `artifacts.transcript` present only with
  `--transcript`.
- No colour, no box drawing beyond `=` and `→`.

## 3. `StopReason`

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum StopReason {
    Completed,                    // {"kind":"completed"}
    MaxPaths { limit: usize },    // {"kind":"max-paths","limit":20}
    Interrupted,                  // {"kind":"interrupted"}
}
impl StopReason {
    pub fn is_partial(self) -> bool;      // !Completed
    pub fn phrase(self) -> String;        // "complete" / "--max-paths 20 reached" / "interrupted by Ctrl-C"
}
```

- Initial value in `run_debug_command`: `StopReason::Completed`.
- Set to `Interrupted` at: the `on_left` stop-flag check, the `on_right` stop-flag check, the
  `if cancelled` block after the left `execute_streaming` (catches `ExecError::Cancelled` from
  `SolverPruner::enter`), and the same `if cancelled` block after the right `execute_streaming`.
- Set to `MaxPaths { limit }` at: the `on_left` and `on_right` `if let Some(m) = opts.max_paths`
  checks (`*explored > m`).
- Assignment is unconditional (last writer wins). In practice a run stops on the first `Break`,
  so at most one site fires; the only overlap (`--max-paths` hit *and* `Ctrl-C`) resolves to
  whichever the executor reaches first, and both labels are defensible.

`trace.json` for a completed default run: `…, "left_syntactic": 6, "stop_reason": {"kind":
"completed"}` (no `partial` key). `is_ok()` unchanged in meaning.

## 4. `flush` / `write_summary` signature change — every call site

`report::flush` and `report::write_summary` both take `elapsed: Duration` as the **second**
argument (`(run, elapsed, out_dir)`).

- `src/debug/driver.rs:670` (`run_debug_command`, end-of-run): `report::flush(&run, started.elapsed(), &out_dir)?`
- `src/debug/driver.rs:801` (`explore_paths`, `on_left`, per left path): `report::flush(run, started.elapsed(), out_dir)`
- `explore_paths` itself gained a `started: Instant` parameter (threaded from `run_debug_command`).

No other crate calls `flush` / `write_summary`.

`run.partial` → `run.partial()` (accessor) at: `is_ok()` body, `render_tree` trailer, and three
driver tests (`max_paths_stops_early_and_flags_partial`, `stop_flag_bails_with_a_partial_run`,
`stop_flag_set_mid_sweep_stops_cleanly`). `DebugEvent::Finished { partial }` →
`{ stop_reason }` at the one emit site (`driver.rs`) and every `progress.rs` match/construct.

## 5. Viewer migration (this is story 13's `T.partial` item — done here)

The template had **one** `if (T.partial)` site (the summary chip), not the two the old spec
mentioned. It now reads:

```js
const stopReason = T.stop_reason || null;
const partial = stopReason ? stopReason.kind !== "completed" : !!T.partial;   // schema-4 fallback
if (partial) {
  let why = "";
  if (stopReason && stopReason.kind === "interrupted") why = " (interrupted by Ctrl-C)";
  else if (stopReason && stopReason.kind === "max-paths") why = ` (--max-paths ${stopReason.limit} reached)`;
  addChip("fail", "PARTIAL — exploration stopped early" + why);
}
```

`index.html` stays self-contained and byte-deterministic (verified: two real runs produce
byte-identical `trace.json` **and** `index.html`).

## 6. Tests

`src/debug/report.rs` (`#[cfg(test)]`, no feature needed):

- `summary_txt_completed_run_shape` — header/status/elapsed strings, greppable `options` line,
  verdict counts == `run.summary`, the goal-fail pair listed with id + model path,
  `explored of 3 syntactic`, no empty `inconclusive` block.
- `summary_txt_stop_reason_status_lines` — `MaxPaths { limit: 20 }` and `Interrupted` produce the
  right `STOPPED EARLY (…)` strings.
- `summary_txt_admitted_is_header_plus_status` — admitted run has `status ADMITTED …`, no
  `paths` / `verdicts` blocks.
- `summary_txt_differs_only_in_the_elapsed_line` — two `elapsed` values, diff the outputs line by
  line, require **exactly one** differing line and it starts with `elapsed`.
- `summary_txt_goal_fail_ids_match_the_trace` — the `goal-fails` ids in `summary.txt` equal the
  `goal-fails` pair ids in `trace.json`; `stop_reason.kind == "completed"`; no `partial` key.

`src/debug/driver.rs` (`#[cfg(all(test, feature = "cvc5-lib"))]`):

- `max_paths_stops_early_and_flags_partial` — now also asserts `run.stop_reason == MaxPaths { limit: 1 }`.
- `stop_flag_bails_with_a_partial_run` — asserts `stop_reason == Interrupted`,
  `trace.json` has `stop_reason.kind == "interrupted"` and no `partial`, and `summary.txt` exists.
- `stop_flag_set_mid_sweep_stops_cleanly` — asserts `stop_reason == Interrupted`, schema 5, and
  the `summary.txt` from the interrupting flush agrees with `run.summary` on the verdict counts
  and the pair count (this is the acceptance criterion "interrupting mid-way leaves a summary
  whose counts match the trace.json written by the same flush").

`src/debug/progress.rs`: `plain_lines_are_terse_and_greppable` final line asserts `(complete)`.

```
cargo build  --workspace                          # clean
cargo build  --workspace --features cvc5-lib       # clean
cargo clippy --workspace [--features cvc5-lib]     # clean
cargo test   -j2 --workspace                       # 133 pass, 4 ignored (pre-existing)
cargo test   -j2 --workspace --features cvc5-lib   # 153 pass, 5 ignored (pre-existing)
```

(`--features cvc5-lib` link is memory-heavy — `CARGO_BUILD_JOBS=2 cargo test -j2`; a full-parallel
run OOM-kills.)

End-to-end verified against `kem-dem/kem-dem-cca-ssp` proofstep 0 (`PKGEN` + `PKENC`,
`same-output`) and `example-projects/hello-world` (`UsefulOracle`, `same-output`): completed,
`--max-paths 3`, and admitted runs all produce the right `summary.txt`; `viewer:` / `smt:`
trailer unchanged; exit code unchanged.

## 7. State handed to the next story

- **`TRACE_SCHEMA = 5.`** `trace.json` gained `left_syntactic: u64` and `stop_reason:
  {"kind": "completed" | "max-paths" (+ `"limit"`) | "interrupted"}`; **`partial` is gone.**
  Whichever of 13 / 14 lands next bumps to 6.
- **`DebugRun.partial: bool` is replaced** by `stop_reason: StopReason` + the `partial(&self) ->
  bool` accessor. Any new code that wants "did it finish" calls `run.partial()`; new code that
  wants the reason matches `run.stop_reason`.
- **`report::flush(run, elapsed: Duration, out_dir)`** — the elapsed time is a parameter, never a
  field of `DebugRun` (story 07 determinism). `run_debug_command` holds `started: Instant` and
  passes `started` to `explore_paths`, `started.elapsed()` to both flushes. Story 14's message
  loop must thread the same value.
- **`DebugEvent::Finished { summary, stop_reason }`** (was `{ summary, partial }`).
- **`summary.txt`** is written on every flush and is **not** byte-deterministic (the `elapsed`
  line). Everything else on it is a pure function of `DebugRun`. Its `options` line prints
  `jobs=1` literally in `render_summary` — story 14 makes it `jobs={n}`.
- **The viewer's `partial` chip already reads `stop_reason`** (with a `T.partial` fallback).
  Story 13 does not need to touch it.
- **`SmtOut::as_str()`** is now public (kebab-case string).
