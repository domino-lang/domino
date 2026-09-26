# Story 39 — implementation report

## What changed

- **`src/writers/easycrypt/progress.rs`**: two new `ExportEvent`s, `LockstepStarted` and `LockstepFinished { found: Option<(joint paths, stuck points)>, elapsed, stopped }`, and a defaulted `ExportObserver::lockstep_observer()` (a `NopObserver`). The progress mode is carried by the export observer, so `run_tactics_observed` keeps its signature. `lockstep_summary_line` renders `  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s` (singular/plural, `failed` when lockstep execution errored, ` (stopped)` after a Ctrl-C).
  - `BarExportObserver`: `lockstep_observer()` is a `debug::progress::BarObserver`, the bar `domino debug` draws. On `LockstepStarted` the proving bar is removed from its `MultiProgress`, so only the debug bar draws; on `LockstepFinished` the summary line is printed and the proving bar is added back.
  - `PlainExportObserver`: two lines per oracle, `  PKENC  lockstep: started` and the summary line; its `lockstep_observer()` stays the null one, so no per-path lines.
  - `NopExportObserver`: nothing. `LoggingExportObserver` forwards `lockstep_observer()`.
- **`src/easycrypt/tactics/live/mod.rs`**: `LiveHandle::lockstep_started`, `lockstep_observer`, `lockstep_finished`, forwarding to the observer it owns.
- **`src/easycrypt/tactics/mod.rs`**: `tactics_for_oracle` hands `run_lockstep_command` that observer instead of `NopObserver`, drops it (its bars are cleared) and only then reports the summary. `lockstep_time` and the final report are unchanged.
- **`src/debug/progress.rs`**: `BarObserver` clears itself on drop as well (a lockstep run that errors before `LockstepFinished` no longer leaves bars), and registers its `MultiProgress` in a process-wide slot. `eprintln_above_bars(msg)` prints through `MultiProgress::suspend`, so the message never tears the bars.
- **`crates/domino/src/main.rs`**: the Ctrl-C handler prints its first message through `eprintln_above_bars` (used by `prove` and `easycrypt debug`).

## Verification

- Unit tests (`writers::easycrypt::progress::tests`): the summary line format; `LoggingExportObserver` forwards `lockstep_observer`; `BarExportObserver` survives two lockstep interludes with the proving bar back each time (stderr is not a terminal in tests, so nothing is drawn).
- `crates/domino/tests/easycrypt_lockstep_progress.rs` (real EasyCrypt, two-oracle project, runs the binary): `--progress plain` prints an even number of lockstep lines, each oracle's pair being `started` then a summary with the same oracle name, and no `debug:` lines; `none` prints no lockstep line; `bar` without a terminal prints none; stdout (minus the timing lines) is identical across the three modes. Run twice, stable.
- By hand under a pty (`script`), `--progress bar` on the two-oracle project: the debug `pairs` line is drawn during each oracle's lockstep execution, then the summary line appears and the `tactics` bar is redrawn under it.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean except `src/debug/sweep.rs:199`, older than this story.
- Full suite (`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`, cvc5 env sourced): without `cvc5-lib` 543 passed, 2 failed, 5 ignored; with it 630 passed, 2 failed, 6 ignored. The two failures are `session::tests::a_stop_request_interrupts_the_running_sentence_at_once` and `the_timeout_still_interrupts_and_is_not_a_stop` (session.rs, which this story does not touch): timing tests that fail in the full parallel run on a machine loaded by other sessions' kem-dem runs and pass alone (`cargo test --lib session::tests`: 13 passed). `easycrypt_ctrl_c` failed once in a full run for the same reason and passed on rerun (4 passed, twice). Every `domino` integration test binary, the new one included, passes.

## Deviations and notes

- **`domino easycrypt debug` is unchanged.** The story says "`prove` (and `debug`)", but `easycrypt debug` has no `--progress` flag today and prints one line per oracle as it finishes; `domino debug` already has the bar. Adding a flag was not asked for, so it still passes `NopObserver`.
- **Not measured on kem-dem.** The hand check was on the two-oracle project, where lockstep execution takes 0.1 s. The multi-second look of the bar (and the elapsed timer) on a large oracle was not seen.
- **Ctrl-C:** the bars are wiped for the interrupt message and drawn again below it; they are gone as soon as lockstep execution stops (the next solver query boundary), so the summary line carries ` (stopped)`. The handler and the bar share a process-wide slot, at most one debug bar at a time.
- `CONTEXT.md` and the overview carry unrelated uncommitted edits, so they are not touched.

## Code review

The `/implement` skill is user-only and could not be invoked; `/code-review` was not run and no sub-agents were spawned. The diff was reviewed by hand against the spec. No finding beyond the one already handled while writing: an error before `LockstepFinished` would leave the debug bars on screen, hence the `Drop`.
