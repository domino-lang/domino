# Story 41 — implementation report

## What changed

- **`src/easycrypt/transcript.rs`**: `GOALS_PER_STEP` 3 to 1, `GOAL_TEXT_CAP` 12 000 to 2 000. Nothing else in the record changed: `goals_dropped` and `text_dropped` are still always written, the byte-offset contract is untouched. Module doc and the `cap_response` example updated.
- **`src/easycrypt/tactics/live/page.rs`**: the note under a step's goals reads `+k goals not kept, see transcript record N` (was `k more goal(s), ...`). The page reads `GOALS_PER_STEP`/`GOAL_TEXT_CAP` from `transcript.rs` as before, so it shows one goal per step from either transcript mode (a `full` transcript is cut to one goal of 2 000 characters when the page reads it back).
- **`crates/domino/src/cli.rs`**: `--ec-transcript` help for `capped`: first goal, cut at 2 000 characters.
- **Docs**: superseded notes in story 31's spec and report and story 28's report; story 33's inherited bullet updated to the new size. `CONTEXT.md` already described the cap as "its first goal" (an unrelated uncommitted edit of the owner's), so it is not touched.

## Measured (kem-dem `--proofstep 0 --oracle PKGEN`, debug build, cvc5-lib)

| | `ec-transcript.jsonl` | records | `index.html` |
|---|---|---|---|
| before (story 31: 3 x 12 000) | 251 773 B | 27 | 73 937 B |
| after (1 x 2 000) | **46 272 B** | 27 | 25 666 B |
| after, `--ec-transcript full` | 4 061 293 B (verbatim) | 27 | 25 665 B |

About 5.4x smaller than story 31's capped transcript. The page of the run has no `goal 2 of` block and carries the `+1`..`+4 goals not kept` notes (`+4` twice, `+3`, `+2`, `+1`). The capped and full pages are identical once timings are stripped.

## Verification

- `transcript::tests`: the 10-goal answer keeps 1 goal and `goals_dropped` 9; new test: a 5-goal answer holds one goal and `goals_dropped: 4`; short/one-goal record kept whole.
- `session::tests`: the capped sink test now expects 1 goal of 2 000 characters, `text_dropped` 48 000, `goals_dropped` 9.
- `tactics::live::tests`: the cut test and the capped-equals-full test use the new note (`+2 goals not kept`, `+4 goals not kept`).
- Clippy `--workspace --all-targets`, with and without `--features cvc5-lib`: clean except `src/debug/sweep.rs:199` (pre-existing).
- Full suite (`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`): without `cvc5-lib` 549 passed (lib), 0 failed, 5 ignored; with it 637 passed (lib), 0 failed, 6 ignored. The timing-sensitive session tests passed.

## Deviations and notes

- **Pre-existing bug found, not fixed:** `easycrypt prove` never writes `Eq_*_Invariants.ec`, because `job::is_proof_file` matches every `Eq_*.ec`, invariants file included, so `ensure_translation_files` skips it and EasyCrypt fails with `cannot locate theory ..._Invariants` on a fresh `_build`. For the measurement I copied the file in from `domino easycrypt` (plain export). Out of this story's scope.
- The note wording is `+k goals not kept, see transcript record N` (the record pointer kept from the old note; "+1 goals" is not singularised, matching the story's literal wording).
- The kem-dem `_build/easycrypt` directory (gitignored) was deleted and regenerated for the measurement.
- Only PKGEN of proofstep 0 was measured, the same run as story 31, so the two figures compare directly.

## Code review

`/implement` and `/code-review` are not available to this agent; the diff was reviewed by hand against the spec. No findings: the constants are the only source of the cap, and every test that quoted 3/12 000 was updated.
