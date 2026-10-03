# Story 44 — `easycrypt debug` shows its stages and progress

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35 (the proof-job subcommands), 39 (the lockstep bar inside `prove`).
**Blocks:** nothing. Story 45 moves `--progress` off the parent command; the two can be done in
either order.

---

## 1. Why this story exists

The owner: *"domino easycrypt debug does not show any progress bars while running the debugger"*,
and: *"I want a proper message explaining phases and if translation is happening to memory or to
disk (if it does not exist)."*

`domino easycrypt debug` is silent on stderr from start to finish:

- `easycrypt_debug` (`crates/domino/src/main.rs`) translates with a `NopExportObserver`;
- `debug_theorem` (`src/easycrypt/debug.rs`) hands `run_lockstep_command` `&mut NopObserver`;
- `EcDebug` has no `--progress` flag. The parent's `domino easycrypt --progress X debug` parses and
  is ignored (story 45 removes that spelling).

Story 39's report records the gap: *"`domino easycrypt debug` is unchanged … it still passes
`NopObserver`."* On kem-dem, both translation and each oracle's lockstep execution are long silent
stretches. The only output is one stdout line per finished oracle.

`prove` shows bars, but it never says what stage it is in or whether it wrote to the export tree.
It prints a bare `created {file} (missing from the translation)` from two places
(`ensure_translation_files` in `src/easycrypt/job.rs` and `tactics_for_oracle`'s proof-file
creation in `src/easycrypt/tactics/mod.rs`).

## 2. Inherited from earlier stories

- **Symbolic-execution stories:** `DebugObserver`, `BarObserver`, `PlainObserver`, `NopObserver`
  (`src/debug/progress.rs`), and the per-target `make_observer` in `domino debug`
  (`crates/domino/src/main.rs`), which creates a fresh observer per oracle and drops it (clearing its
  bars) before printing that oracle's `one_line()`.
- **Story 21:** `export_observer(mode)` and the export's `BarExportObserver` /
  `PlainExportObserver`, which `prove` uses for translation.
- **Story 35 / ADR 0006:** a proof job needs translation's result in memory and never rewrites a
  translation file. `easycrypt debug` reads no file of the export tree and writes only `!debug!/`.
- **Story 39:** `eprintln_above_bars`, and the Ctrl-C handler already prints through it.
- **Story 36:** parallel proof jobs. `create_if_absent` already tolerates two jobs creating the same
  translation file.
- **`resume-an-oracle-from-its-saved-joint-tree` (ADR 0008):** `tactics_for_oracle` now starts
  with `resuming(…)`. An oracle the session record holds as `interrupted` is walked on its saved
  joint tree **without lockstep execution** (no `LockstepStarted`/`LockstepFinished` events, no
  lockstep bar); `LiveHandle::oracle_resumed` marks it on the page instead. Lockstep execution moved
  into `lockstep(…)`, which also writes `Eq_<L>_<R>.<oracle>.tree.json` (`save_tree`). The resume
  warnings (no tree, version 2 record, stale tree, a replayed sentence rejected, a tree not saved)
  are plain `eprintln!`s in `resuming`/`save_tree` (`tactics/mod.rs`) and `keep_node`/`replay`
  (`tactics/driver.rs`), not routed above the bars: candidates for this story's stage messages.

## 3. Work to do

**Stage** (see `CONTEXT.md`) means a command-level step: translation, lockstep execution, proving,
report. It is not an `ExportPhase`, which is a step *inside* translation and is what the export bar
already names. The stage messages below describe the action and do not print the word "stage".

### 3.1 `easycrypt debug`: progress

- `EcDebug` gets `--progress` (`ProgressMode`, default `auto`), with the same help text as
  `EcProve`'s.
- Translation uses `export_observer(d.progress)` instead of `NopExportObserver`, exactly as `prove`
  does.
- `debug_theorem` takes a factory for the debug observer, `&mut dyn FnMut() -> Box<dyn
  DebugObserver>`, the same `make_observer` shape `domino debug` has. It creates one observer per
  oracle, passes it to `run_lockstep_command`, and **drops it before calling `on_finished`**, so the
  stdout line never lands on a half-cleared bar.
- Plain mode follows `domino debug`'s convention, not `prove`'s: one stderr line per
  `(left, right)` pair. This is the debugger, and path-level detail is what it is for.
- No outer "oracle k/N" bar. The stdout lines already count finished oracles.
- Fix `debug_theorem`'s doc comment: it says the export is "already written to `theorem_out`",
  which is false. Nothing of the tree is read or written.

### 3.2 `easycrypt debug`: stage messages

On stderr, through `eprintln_above_bars` (or the bar's `MultiProgress::println`), in `auto`, `bar`
and `plain`, and not in `none`. Every line starts with the command name, so it can be grepped:

```
easycrypt debug: translating KEMDEMSecurity in memory (the export tree is not read or written)
  …translation bar…
easycrypt debug: lockstep execution on 7 oracles of 3 equivalences → _build/easycrypt/KEMDEMSecurity/!debug!/
  …one debug bar per oracle; stdout gets each oracle's one_line as today…
```

- `easycrypt debug` keeps its contract: it **never** creates a missing translation file, so its
  translation line always says "in memory". It runs no EasyCrypt and has no use for the files.
- The oracle and equivalence counts are those the run will actually visit after `--proofstep` and
  `--oracle`, counted before the first oracle starts.
- One translation line per theorem (a proof job is given one theorem, so in practice one line).

### 3.3 `prove`: stage messages

`prove` announces its stages the same way, so the two proof jobs read alike:

```
easycrypt prove: translating KEMDEMSecurity in memory
  …translation bar…
easycrypt prove: Eq_Real_Ideal — wrote missing translation files: Eq_Real_Ideal_Invariants.ec, Eq_Real_Ideal.ec
easycrypt prove: Eq_Hyb_Ideal — translation files already on disk
```

- **The translation line never mentions disk.** Missing files are not created during translation.
  They are created per equivalence, after its proof lock is taken and `plan_job` has decided not to
  skip it (`tactics/mod.rs`, around `ensure_translation_files`). Only then does the process know what
  *it* wrote. A pre-check at translation time would be wrong for skipped equivalences and for
  parallel jobs.
- **One line per equivalence that is proved**, printed once both `ensure_translation_files` and the
  proof-file creation have run. It covers the shared translation files and the equivalence's own
  `Eq_*.ec`, and **replaces** both `created … (missing from the translation)` lines.
  - Names the files when fewer than 6 were written, and gives a count otherwise:
    `wrote 14 missing translation files`.
  - When nothing was written: `translation files already on disk`.
  - With `--force` the proof file is restarted from the skeleton. That is not a missing file, so it
    is not listed.
- **A skipped equivalence prints nothing new.** It writes nothing, and its story-35 skip line
  already explains why.
- The live page's `translation_line` (`tactics/mod.rs`) is unchanged.
- `check-alignment` is out of scope.

### 3.4 Not in this story

`domino easycrypt --progress X <subcommand>` is accepted and ignored for every subcommand. Story 45
moves `--progress` onto `export`, which turns that spelling into a parse error.

## 4. Acceptance criteria

- [ ] On a TTY, `easycrypt debug` on a kem-dem theorem shows the translation bar, then one debug bar
      per oracle, each cleared before that oracle's stdout line.
- [ ] `easycrypt debug --progress plain` prints the two stage lines, then `PlainObserver`'s per-pair
      lines.
- [ ] `--progress none` prints nothing new on stderr, for both `debug` and `prove`.
- [ ] stdout is byte-identical across `auto`, `plain`, `bar` and `none`, for both commands (minus
      timing lines, as in story 39's test).
- [ ] The files under `!debug!/` are the same as before this story.
- [ ] A Ctrl-C during `easycrypt debug`'s lockstep execution clears the bar before the interrupt
      message.
- [ ] `prove` on a fresh `_build/easycrypt` prints one `wrote missing translation files: …` line for
      each equivalence: the first lists the shared translation files and its own `Eq_*.ec`, and later
      ones list only their own `Eq_*.ec`. No `created … (missing from the translation)` line remains.
- [ ] `prove` on an equivalence with a complete session record prints no translation-files line for
      it.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt debug --theorem <T> --proofstep 0                      # under a TTY: bars
$D easycrypt debug --theorem <T> --proofstep 0 --progress plain 2>&1 >/dev/null | head
$D easycrypt debug --theorem <T> --proofstep 0 --progress none 2>&1 >/dev/null | wc -l   # 0 new lines
rm -rf _build/easycrypt && $D easycrypt prove --theorem <T> --progress plain 2>&1 >/dev/null | grep 'easycrypt prove:'
```

Extend `crates/domino/tests/easycrypt_lockstep_progress.rs` (or add a sibling) to cover `debug`'s
modes and `prove`'s translation-files lines on the two-oracle project. Never run either command on
4WHS or yao.
