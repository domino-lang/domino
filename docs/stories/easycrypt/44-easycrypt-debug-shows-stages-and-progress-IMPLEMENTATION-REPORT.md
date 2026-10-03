# Story 44 — implementation report

## What changed

- **`crates/domino/src/cli.rs`**: `EcDebug` has `--progress` (`ProgressMode`, default `auto`), with
  `EcProve`'s help text.
- **`crates/domino/src/main.rs`**
  - `debug_observer(mode)` builds one `DebugObserver` (bar on a TTY, per-pair lines when piped,
    nothing for `none`). `domino debug`'s `make_observer` now calls it, so both debuggers share it.
  - `stage_line(mode, line)` prints through `eprintln_above_bars`, and nothing under `none`.
  - `easycrypt debug`: translates with `export_observer(d.progress)`. Its stage lines:
    `easycrypt debug: translating <T> in memory (the export tree is not read or written)` and
    `easycrypt debug: lockstep execution on N oracle(s) of M equivalence(s) → <theorem_out>/!debug!`.
    It passes `debug_theorem` a factory, `&mut || debug_observer(d.progress)`.
  - `easycrypt prove`: prints `easycrypt prove: translating <T> in memory` before translation and
    sets `TacticsOptions.announce_stages` unless `--progress none`.
- **`src/easycrypt/debug.rs`**
  - `debug_theorem` takes `make_observer: &mut dyn FnMut() -> Box<dyn DebugObserver>`. It makes one
    observer per oracle and drops it before `on_finished`, so the stdout line never meets a half-cleared
    bar. The doc comment no longer claims the export is "written to `theorem_out`".
  - `select(…)` is the one selection (`--proofstep`, `--oracle`, `NoSuchOracle`) shared by the run and
    by the new `plan_debug(theorem, exported, options) -> DebugPlan { equivalences, oracles }`, which
    `main` calls to say the counts before the first oracle starts.
- **`src/easycrypt/tactics/mod.rs`**
  - `TacticsOptions.announce_stages` (default `false`).
  - `tactics_for_equivalence` takes the shared files `ensure_translation_files` created, creates the
    equivalence's `Eq_*.ec` if missing, and prints one `translation_files_line` through
    `eprintln_above_bars`: `wrote missing translation files: a, b` (fewer than 6, i.e.
    `NAMED_FILES_LIMIT`), `wrote N missing translation files`, or `translation files already on
    disk`. With `--force` the restarted proof file is not listed. A skipped equivalence prints
    nothing new. `translation_line` (live page) is unchanged.
  - The resume warnings (`resuming`, `save_tree`, and `keep_node`/`replay` in `driver.rs`) go through
    `eprintln_above_bars` now, so they no longer tear a bar.
- **`src/easycrypt/job.rs`**: `ensure_translation_files` no longer prints `created …`; it returns the
  paths and the caller reports them. The proof-file `created … (missing from the translation)` line is
  gone too.
- **Tests**
  - New `crates/domino/tests/easycrypt_stage_messages.rs` (3 tests): `debug` in the four modes (stage
    lines and their order, `none` silent, stdout and `!debug!` file lists identical, nothing written
    outside `!debug!`); `prove` on the two-oracle project (translating line, files line, no `created`,
    a complete record prints no files line, `none` silent, stdout identical); `prove` on
    `simple-KEM-example` (two equivalences: the first counts 15 shared files, the second lists only its
    own `Eq_*.ec`).
  - Unit test `the_translation_files_line_names_few_files_and_counts_many` (tactics tests).
  - `easycrypt_prove.rs`: the two assertions on the old `created …` line now check the new line, run
    with `--progress plain`; its helper does not add `--progress none` when the args carry one.

## Verification

`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`, cvc5 env sourced.

| Binary | `cargo test --workspace` | `--features cvc5-lib` |
|---|---|---|
| lib (`sspverif`) | 598 passed, 5 ignored | 696 passed, 6 ignored (second run) |
| `debug_all_claims` | 3 | 4 |
| `easycrypt_ctrl_c` | 0 | 4 |
| `easycrypt_lockstep_progress` | 0 | 1 |
| `easycrypt_overwrite` | 7 | 7 |
| `easycrypt_progress` | 1 | 1 |
| `easycrypt_prove` | 0 | 5 |
| `easycrypt_stage_messages` | 0 | 3 |
| `easycrypt_tactics_writes` | 0 | 3 |
| `sspverif_smtlib` | 2 | 2 |

- The first `cvc5-lib` run had one failure, `session::tests::an_interrupt_never_answered_is_unresponsive_after_six_signals`
  (a timing test in `session.rs`, which this story does not touch, on a loaded machine). Alone,
  `cargo test --lib session::tests` passed 16/16, and a full rerun passed everything.
- `cargo clippy --workspace --all-targets`, with and without `cvc5-lib`: only the warnings that
  predate this story (`src/debug/sweep.rs:199`, the `TempDir::into_path` deprecations).
- By hand under a pty (`script`), `easycrypt debug --progress bar` on the two-oracle project: the
  translation bars, then the lockstep stage line, then one debug bar per oracle, each cleared before
  that oracle's stdout line.
- `prove` on `simple-KEM-example` from an empty `--out` (31 s): `wrote 15 missing translation files`
  for the first equivalence, `wrote missing translation files: Eq_H1_kem_correctness_ideal_H2.ec` for
  the second.

## Deviations and notes

- **The translation-files line for the first equivalence counts** on a fresh tree, because the
  shared files plus the `Eq_*.ec` are 6 or more on any real project. The story's rule (name below 6,
  count otherwise) was followed as written.
- **`ensure_translation_files` writes every non-proof file at the first equivalence**, including the
  other equivalences' `_Invariants.ec`; so later equivalences list only their own `Eq_*.ec`, as the
  acceptance criterion expects.
- **`debug` exits non-zero on the two-oracle project** (`ChangeNameUsefulOracle` fails the invariant),
  so the debug test tolerates a failing exit and cuts stderr at the `Error:` line.
- The Ctrl-C message was already printed through `eprintln_above_bars` (story 39), so no handler
  change; not exercised on a TTY by hand.
- Resume warnings in `plan_job` (`skip_line`, `resume_line`) stay plain `eprintln!`: no bar exists yet
  there.

- **Resume warnings rerouted.** Routing them above the bars was not in §3; it follows §2's note that
  they are candidates for this story, and costs one line per site.

## State handed to the next story

- `EcDebug` has `--progress`; the parent `domino easycrypt --progress X debug` still parses and is
  ignored. Story 45 moves `--progress` off the parent for translation only. Facts for it are in its §2.
- `stage_line`, `debug_observer`, `plan_debug`, `DebugPlan` and `TacticsOptions.announce_stages` are
  new.

## Notes for follow-up

- `stage_line` and `export_observer` mode matching live in `main.rs`; nothing else uses them.
- `check-alignment` still prints no stage messages (out of scope).

## Code review

`/code-review` against 59fb917b, Standards and Spec axes in parallel.

- **Standards:** no documented-standard breach. Judgement calls, left as they are: `translation_files_line`
  beside `translation_line` (they differ in wording and one has a limit), the `progress != None` test
  appearing in `stage_line` and in `announce_stages`, `plan_debug` transforming the theorem a second time
  (cheap), and `#[allow(clippy::too_many_arguments)]` on `debug_theorem`. The one actionable point,
  that the warning rerouting was not mentioned, is now in *Deviations and notes*.
- **Spec:** nothing missing. Unverified by test: Ctrl-C on a TTY during `easycrypt debug` (the handler
  already prints above the bars, story 39). The stage line says `1 oracle of 1 equivalence` in the
  singular, which the story's example does not show; kept.
