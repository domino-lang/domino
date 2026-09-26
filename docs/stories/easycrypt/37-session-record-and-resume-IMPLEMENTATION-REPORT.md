# Story 37 — implementation report

## What changed

- **`src/easycrypt/job.rs`**: the record is version 2.
  - `SessionRecord` gains `domino` and `updated` (RFC 3339 UTC, formatted by hand, no new dependency). Both default to empty when a version-1 record is read.
  - `OracleRecord` gains `script` (done oracles only), `admits` (`node`, `reason`, and the extra `claim` and `domino` slugs, so the report can be rebuilt), `lockstep` (`joint_paths`, `ms`) and `nodes` (`NodeRecord {id, tactics}`).
  - `OracleRecord::is_resumable` = done with a script. `OracleRecord::new(name, status)` builds a bare entry.
  - `skip_line` is for a complete record only. New `resume_line` (`resuming Eq_L_R: 2 of 5 oracles already proved`) and `version_1_line`.
- **`tactics/script.rs`, `driver.rs`**: every accepted sentence is tagged with the joint node the walk was in (`Script::set_node`, called from `prove_node`). `Script::by_node` groups them (`N<k>` or `router`) and `Sealed::node_scripts` carries them out. `AdmitReason::from_slug` and `DominoView::from_slug` read a record's slugs back.
- **`tactics/mod.rs`**:
  - `plan_job` returns `JobPlan::Skip` or `JobPlan::Prove { prior }` by the §3.2 table. `prior` is the record whose done oracles are resumed and whose other entries are kept.
    - With `--force` and no `--oracle` the record is deleted (from scratch). With `--force --oracle O`, `O`'s entry is reset and the others stay, and the proof file is not restarted from the skeleton.
    - Without `--force`, `--oracle O` skips when `O` is done, and proves `O` when not.
  - `OracleTactics::from_record` / `to_record`, and the fields `node_scripts` and `resumed`. An entry with an unknown reason or verdict slug is not resumable and is proved again.
  - `tactics_for_equivalence`: resumed oracles are seeded into the proof file's oracle list before the walk, so every write from the first checkpoint on holds their scripts. In the walk, a goal of a resumed oracle gets `admit.` only: no lockstep execution, no other sentence.
  - `ProofFile::record` writes each oracle's entry from its result, and keeps the prior entry for an oracle this run has not reached (so `--oracle O` keeps the others' scripts, `interrupted` and `pending` included).
- **Report and page**: a resumed oracle is `NAME: resumed from session record (lockstep N joint paths, K admits)`, followed by its admits. The page shows the chip `resumed from session record` and a note.
- `cli.rs`: `--oracle` and `--force` help.

## Verification

- Unit tests, no EasyCrypt (`job::tests`, `tactics::tests`, `script::tests`): record round trip and version 1 read, timestamp formatting, the whole §3.2 table through `plan_job` (none, complete, partial, `--force`, `--oracle O` with and without `--force`, version 1), `from_record` / `to_record`, node grouping.
- Real EasyCrypt, two-oracle project (`tactics::tests::live`, need `DOMINO_EASYCRYPT`):
  - Stop at the second oracle (the Ctrl-C case), then run again. Only the second oracle is walked: one `proc; inline.` after the `call` in the transcript. The first oracle's script is byte-identical in the file. The report and page say `resumed from session record`. The record is complete with both scripts. The resumed file compiles with `easycrypt compile`.
  - A complete record skips; `--oracle O --force` proves only `O` and gives the same file; `--force` proves both again.
  - The file written and the record missing (the kill -9 state): the job proves from scratch, ends with a complete record and a compiling file.
  - A version-1 record: nothing resumed, both oracles proved, the record is rewritten as version 2.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean except `src/debug/sweep.rs:199`, which is older than this story.
- Full suite (`DOMINO_EASYCRYPT` absolute; cvc5 env sourced): without `cvc5-lib` 542 passed, 5 ignored; with it 629 passed, 6 ignored; no failures.

## State handed to the next story

- Record size on `hello-world-oracle-rename-new` (2 oracles): 1.6 KB, against a 1.5 KB `Eq_*.ec`. It repeats each script plus the per-node sentences, so about twice the proof file. **Not measured on kem-dem's largest equivalence**: a run there takes minutes per oracle and was not done. At node granularity the record is rewritten with every write, so its size grows with the proof; if that matters, the `nodes` lists are the part to drop first.
- `ProofFile::write` is the one place that writes the file, report and record. `OracleTactics::to_record` builds an oracle's entry from a sealed partial too, so story 38's per-sentence checkpoints need no new plumbing.

## Deviations and notes

- **Write order** stays report, then file, then record (story 33's order, its reason is in the code), not file, report, record as §3.4 says. The crash property that matters, the record never claiming more than the file holds, is unchanged.
- **Admit entries carry `claim` and `domino` too**, beyond `node` and `reason`, so a resumed report line reads as the original did. The admit's goal text is not kept, so a resumed `domino-verified-ec-failed` admit has no goal in the report.
- **A resumed oracle's report line is short**: closed goals, fallbacks and EasyCrypt time are not in the record, so they are not shown (not shown as zeros).
- **An oracle that ended with a `problem`** (lockstep failed) is `done` with an empty script, as it was before, so resume never retries it; `--force --oracle O` does.
- **Not-selected oracles with an `interrupted` entry**: with `--oracle O`, their entry is kept, but the file has the skeleton bullet again (the sealed partial text is not kept in the record, only its `nodes`).
- **Skip line wording** for `--oracle O` already done: `skipping <Eq_L_R> ...`-style line names the oracle; a complete record uses the story-35 line.
- ADR 0004's *Resuming is not addressed* bullet already carried the pointer to ADR 0006 and this story (an uncommitted edit in the tree); it is committed with this story. `CONTEXT.md` has no term added for the resume behaviour; it has unrelated uncommitted edits, so it is left for its owner.
- No CLI-level test of the skip and resume lines on stderr: they are covered through `plan_job` and the library-level runs.

## Code review

The `/code-review` skill was not run (no sub-agents were spawned); the diff was reviewed by hand against the spec. Nothing further found beyond the notes above.
