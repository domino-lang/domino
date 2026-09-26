# Story 38 — implementation report

## What changed

- **`src/easycrypt/tactics/mod.rs`**: `WriteGranularity::Tactic`, and it is the `TacticsOptions` default. `tactics_for_oracle` hands the same `write_sealed` closure to the prover under `node` and `tactic`; `Prover::per_sentence` says which. `ProofFile` counts its writes (`Cell`), and `EquivalenceTactics::writes` exposes the count at the last write.
- **`tactics/driver.rs`**: under `tactic`, `Prover::send` calls `checkpoint()` after every sentence EasyCrypt accepts, and so does `Prover::admit` (an accepted `admit.` is a sentence too). Rejected, timed-out and interrupted sentences return before the push, so they never write and never enter the file. `prove_node` skips its own end-of-node write under `tactic`: the write after the node's last accepted sentence already holds the same file, so that write would only duplicate one.
- **`cli.rs`, `main.rs`**: `--write-granularity tactic`, the default; help text updated (`oracle` and `node` keep their meaning).
- The write itself is unchanged: report, then file, then session record (story 37), each atomic, so every write is a sealed, whole proof and a record that claims no more than the file holds.

## Verification

- `tactics::tests::live::at_tactic_granularity_every_accepted_sentence_is_written` (real EasyCrypt, two-oracle project): writes equal the accepted walk sentences in the transcript plus one per oracle plus the final one, and exceed the `node` run's writes; the rejected count is reported in the failure message only; every file captured at an event is a whole proof; the final file compiles and has no `interrupted`.
- `easycrypt_tactics_writes::a_run_killed_at_the_default_granularity_...`: `prove` with no granularity flag, `kill -9` once a sealed write and the record are both on disk, `easycrypt compile` of the file succeeds, the record exists, and the next `prove` resumes and finishes with no `interrupted` admit. Run three times, stable.
- Story 33's tests stay on explicit `oracle` / `node`, unchanged.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean except `src/debug/sweep.rs:199`, older than this story.
- Full suite (`DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`, cvc5 env sourced): without `cvc5-lib` 542 passed, 5 ignored; with it 629 passed, 6 ignored; no failures.

## kem-dem proofstep 0, tactic against node (AC 3)

**Not measured to completion.** The equivalence (`kem_dem_cca_ssp`, `Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM`) did not finish in either run within a 900 s cap (debug build of `domino`, sequential runs). At the cap both had sent the same 247 sentences (transcript lines), so no throughput difference is visible. A full run to completion was not done; the 5% bound is therefore unconfirmed. The two files at the cap:

| granularity | `Eq_*.ec` | session record |
|---|---|---|
| tactic | 6.9 KB | 10.5 KB |
| node | 5.3 KB | 7.2 KB |

The `tactic` file is bigger because more of the oracle in flight is written (it is sealed later in the walk, at the cap), not because of a per-write overhead.

## State handed to the next story

- The record is rewritten per accepted sentence, so at kem-dem sizes it is about 1.5 to 2 times the proof file (10.5 KB at 247 sentences). If the 5% bound fails on a long run, profile the rendering and serialisation of the record first; the `nodes` lists are the part to drop first (story 37).
- Each write does `sync_all` on three files. That was not a visible cost in the runs above.

## Deviations and notes

- **The end-of-node write is skipped under `tactic`** (it would duplicate the last sentence's write). One consequence: after a rung that is accepted and then undone, the file on disk still holds those sentences until the next accepted sentence or oracle end; it is still a proof EasyCrypt accepts, as the story allows.
- **AC 3 (5% on kem-dem) and the kem-dem `kill -9` from AC 2** are not done at kem-dem scale; the kill is tested on the two-oracle project (see above).
- `CONTEXT.md` and the overview carry unrelated uncommitted edits, so they are not touched. No doc other than the CLI help mentioned the granularities.

## Code review

The `/implement` and `/code-review` skills could not be invoked (the first is user-only; no sub-agents were spawned), so the diff was reviewed by hand against the spec. One finding, fixed: `admit` also had to checkpoint, because an accepted `admit.` is a sentence; the write count test caught it.
