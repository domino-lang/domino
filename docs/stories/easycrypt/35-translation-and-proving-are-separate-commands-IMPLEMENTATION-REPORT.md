# Story 35 — implementation report

## What changed

- **The command shape** (`crates/domino/src/cli.rs`, `main.rs`):
  - Plain `domino easycrypt [--theorem T] [--out DIR] [--force] [--progress …]` is translation only. It runs no EasyCrypt.
  - `--tactics`, `--check-alignment` and `--debug` are removed, not aliased. Clap rejects them as unknown.
  - New subcommands `prove`, `check-alignment` and `debug` (`EasycryptCommand`). `--theorem` is required in each.
  - `--project` and `--out` are `global`, so they work before or after the subcommand.
  - `prove` takes `--force|-f`, `--proofstep`, `--oracle`, `--ec-timeout`, `--leaf-budget`, `--no-rung0`, `--ec-transcript`, `--write-granularity` and `--progress`.
  - `main.rs` is split into `easycrypt_translate`, `easycrypt_prove`, `easycrypt_check_alignment` and `easycrypt_debug`. `export_in_memory` and `export_observer` are shared.
- **`src/easycrypt/job.rs`** (new): what a proof job may assume and touch.
  - `create_if_absent(path, text)` writes a temporary file in the same directory, `hard_link`s it to the target, then removes the temporary. `AlreadyExists` is success (`Ok(false)`). It never renames.
  - `ensure_translation_files` creates every file of the export except `Eq_*.ec` that is missing, and prints `created X (missing from the translation)` on stderr. It never reads a file that exists.
  - `SessionRecord` (`Eq_<L>_<R>.session.json`, version 1) holds `theorem`, `left`, `right`, `complete` and `oracles: [{name, status}]`, with statuses `done`, `interrupted` and `pending`. It also has the skip line and `read`.
  - `remove_session_records` deletes every `*.session.json` under a directory.
- **`tactics/mod.rs`**:
  - `TacticsOptions::force`.
  - `plan_jobs` runs before anything is created or truncated:
    - An equivalence with a record is skipped with `skipping Eq_L_R: already proved (k of n oracles)[, resuming arrives with story 37]; --force re-proves it`.
    - If nothing is left to prove, `run_tactics_observed` returns without touching `progress/`, so the earlier run's transcript and page survive.
    - With `--force`, the record is deleted and the proof file is restarted from the skeleton, atomically.
  - `ensure_translation_files` runs once per job.
  - This equivalence's own `Eq_*.ec` is created from the skeleton if absent. Other equivalences' files are never created.
  - `ProofFile::write` now writes the session record after the proof file, atomically.
    - Status is `interrupted` if the oracle has an `interrupted` admit, `done` if it ended otherwise, and `pending` if not reached.
    - No record is written while every oracle is still pending. A run stopped before any oracle therefore leaves no record and can be re-run without `--force`.
- **Translation** (`--force`): deletes every `*.session.json` under each theorem's directory, after the in-memory export succeeded and before the write. ADR 0004's check needed no change, because `*.session.json` is not a run artifact and so already blocks a plain run without `--force`.
- **§3.6, lockstep output follows `--out`:** `tactics_for_oracle` and `debug_theorem` already passed `Some(debug_dir(<out>/<theorem>, …))` when this story started. The story text (`None`) was out of date. Tests now cover it: `!debug!/` appears under the `--out` used.
- **Old flags in code and docs:** comments, error messages and the lockstep summary title (`domino easycrypt debug — summary`) now name the subcommands. Earlier stories' documents are history and are left as they are.

## Verification

- Unit tests (`job::tests`):
  - two threads create the same file, both succeed, exactly one creates it, the file is complete, and no temporary is left behind (20 rounds of 2.6 MB);
  - an existing file is never replaced;
  - the record round-trips, and both skip lines are as specified;
  - `remove_session_records` deletes every record, including in subdirectories, and nothing else.
- `crates/domino/tests/easycrypt_prove.rs` (real EasyCrypt, skipped without `DOMINO_EASYCRYPT`):
  - hello-world: `prove --proofstep 0` needs no `--force`, and every other file has the same bytes and mtime afterwards.
    - Its own `.ec`, report and record appear, and `!debug!` is under `--out`.
    - A second run prints the skip line and changes nothing.
    - With `Types.ec` removed, `-f` prints the `created` line, recreates it and re-proves.
    - Garbage in `Types.ec` is not read: EasyCrypt's `parse error` is reported and the file is left alone.
  - simple-KEM-example (2 equivalences): `prove --proofstep 0` creates the missing translation file and its own skeleton, and not the other equivalence's `Eq_*.ec`.
  - `check-alignment` and `debug` produce the old outputs on hello-world (`1 oracles checked, 0 mismatches`, `alignment.txt`, `UsefulOracle: 1 joint paths, ok`), with `--project` and `--out` after the subcommand, and neither rewrites the translation.
- `easycrypt_overwrite.rs`:
  - the old flags are rejected;
  - a session record makes plain `domino easycrypt` refuse, and `--force` deletes it.
  - The test "the overwrite check comes before the EasyCrypt probe" is removed: the plain command has no probe any more.
- `easycrypt_ctrl_c.rs` and `easycrypt_tactics_writes.rs` now translate first and then run `prove`. The Ctrl-C test also checks the record (`complete: false`, `interrupted`).
- `debug_all_claims.rs`: `easycrypt debug --claim` is still rejected.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean, except `src/debug/sweep.rs:199` (collapsible `if`), which is older than this story and untouched.
- Full suite (`DOMINO_EASYCRYPT` an absolute path):
  - without `cvc5-lib`: all pass (527 passed, 5 ignored);
  - with `--features cvc5-lib`: all pass (611 passed, 6 ignored). The known `goal_smt_is_empty_for_an_admitted_claim` failure of stories 23–34 passed this time.
  - A relative `DOMINO_EASYCRYPT` breaks the unit tests that spawn EasyCrypt (their cwd is not the workspace root). Use an absolute path.

## State handed to the next story

- **Cost of the in-memory translation per `prove`, kem-dem (debug build):**
  - the export itself is about 0.3 s, and plain `domino easycrypt` takes 0.34 s in total;
  - a `prove` that stops right after the setup (`--oracle NoSuchOracle`) takes 0.86 s, which includes the EasyCrypt start-up probe.
  - Restricting the translation to one equivalence is not worth it. The proof itself takes minutes.
- **Places that still assume one tactics run per theorem** (story 36 moves them):
  - `progress/ec-transcript.jsonl` is created and truncated by every run (`run_tactics_inner`), so two jobs on one theorem overwrite each other's transcript.
  - The live page `progress/index.html` and its `LiveHandle` are one per theorem run.
  - The temporary files of `write_atomically` are `progress/.<name>.tmp`, so two jobs writing files of the same name would collide (names differ per equivalence today, so it holds).
  - `check_export_tree` and the run-artifact rules treat `progress/` as shared.
  - `run_tactics_inner` breaks out of the loop over equivalences at the first interrupted one, and `main` exits 130 after the first theorem's report.
- **For story 37:** `SessionRecord` is the minimal form. `plan_jobs` skips on any record and mentions story 37 for a partial one. `ProofFile::record` is where per-oracle scripts and nodes go, and `plan_jobs` is where a partial record turns into a resume.

## Deviations and notes

- The record is pretty-printed JSON, not the one-line form in §3.4. The fields are the same.
- A run that ends before any oracle is reached writes no record (see above). Otherwise it would need `--force` to run again.
- An unreadable or corrupt record is an error that names `--force`, not a silent re-prove.
- `check-alignment` creates the missing translation files (it starts EasyCrypt against them) but not any `Eq_*.ec`. `debug` starts no EasyCrypt and reads no file of the tree, so it writes only `!debug!/`.
- 4WHS and yao stay off-limits for `prove` and `debug`; nothing changed there.

## Code review

- Spec review: one finding fixed. The proof file was created (or, with `--force`, overwritten with the skeleton) before `--oracle` was validated, so a typo wrote a skeleton. The write now comes after the check.
- Left as is, deliberately:
  - `--oracle X` runs record the other oracles as `pending`, so a later `--oracle Y` run is skipped (§3.4 says pending is "not reached"; story 37 resumes them).
  - `prove` starts the EasyCrypt probe and builds the in-memory export even when it will only skip (§3.2 allows it).
- Standards review: no hard violations. Judgement calls not taken: a `flatten` struct for the repeated `--theorem/--proofstep/--oracle` flags, a shared test-helper module, and folding the three proof-job setups in `main.rs`. All are refactors of a size this story does not need.
