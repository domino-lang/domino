# Story 39 — Path exploration has its own progress bar

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35 (the `prove` command), but touches none of its logic.
**Blocks:** nothing.

---

## 1. Why this story exists

The owner: *"the domino easycrypt command does not indicate the time spent on the path exploration
phase at the beginning of the oracle … I want a progress bar similar to the debug command progress
bar for the exploration phase!"*

Every oracle starts with lockstep execution, and on a large oracle that is the longest silent
stretch of the run. `tactics_for_oracle` passes `&mut NopObserver` to `run_lockstep_command`, so
nothing is shown; the time is measured (`lockstep_time`) but only surfaces in the final report.

## 2. Inherited from earlier stories

- **Symbolic-execution stories:** `DebugObserver`, `BarObserver` and `PlainObserver`
  (`src/debug/progress.rs`), the bar `domino debug` shows, driven by `DebugEvent::JointNode`,
  `JointPairChecked`, `StuckPointFound`, `LockstepFinished`, `Totals`.
- **Story 21:** the export's `BarExportObserver`/`PlainExportObserver`
  (`src/writers/easycrypt/progress.rs`), which is what `prove` draws its own bar with.

## 3. Work to do

- `prove` (and `debug`) hands `run_lockstep_command` the same observer `domino debug` would get for
  the chosen `--progress` mode, instead of `NopObserver`.
- **Bar mode:** while lockstep execution runs, the debug bar is shown with the elapsed time, and the
  proving bar is hidden. Both are indicatif bars on stderr; they must share one `MultiProgress`, or
  the proving bar must be suspended, so the two do not overwrite each other's lines.
- When lockstep execution ends, its bars are cleared and one line is printed above the proving bar:
  `  PKENC  lockstep: 23 joint paths, 1 stuck point in 41.2s`.
- **Plain mode:** no per-path lines (they would flood a log). One line when lockstep execution
  starts and the summary line above when it ends.
- A Ctrl-C during lockstep execution (story 34) clears the bars before the interrupt message.
- The final report keeps its per-oracle lockstep time.

## 4. Acceptance criteria

- [ ] On a TTY, `prove` on a kem-dem equivalence shows the debug bar during each oracle's lockstep
      execution and the summary line afterwards.
- [ ] `--progress plain` prints exactly two lockstep lines per oracle.
- [ ] `--progress none` prints nothing new; stdout is byte-identical across modes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt prove --theorem <T> --proofstep 0 -f
$D easycrypt prove --theorem <T> --proofstep 0 -f --progress plain 2>&1 | grep lockstep
```
