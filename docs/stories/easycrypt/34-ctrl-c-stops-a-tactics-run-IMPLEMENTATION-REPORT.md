# Story 34 — implementation report

## What changed

- **The handler** (`crates/domino/src/main.rs`): `stop_on_ctrl_c(message)` installs the Ctrl-C
  handler of `domino debug`, now shared by both commands.
  - The first press sets an `Arc<AtomicBool>` and prints one line. The second press exits 130.
  - An already installed handler is not fatal.
  - `easycrypt()` installs it only when it builds the `TacticsOptions`, after the export (§3.5).
  - After the report of a theorem whose result is interrupted, the summary is printed, stdout is
    flushed, and the process exits **130**.
- **`TacticsOptions::stop: Option<Arc<AtomicBool>>`** (default `None`). The run passes it to:
  - `run_lockstep_command`, which stops at its next node. The in-flight cvc5 query cannot be
    cancelled.
  - `Session::set_stop`.
- **`Session`** (`src/easycrypt/session.rs`):
  - `set_stop(flag)` and `stop_requested()`.
  - While a sentence runs, `wait_line` checks the flag every 100 ms (`STOP_POLL`). The ticks for
    the observer are unchanged. When it sees the flag, the sentence is interrupted as a timeout
    would interrupt it (`Session::interrupt`, `INTERRUPT_GRACE`).
  - Two kinds of sentence are never interrupted by a stop, so rolling back always works:
    - sentences sent once the flag is already set;
    - `undo_to` (`exchange(…, stoppable = false)`).
  - `SessionEvent::Answered` has a new field `stopped: bool`. It is true when the sentence was
    interrupted because of the stop, and false when the timeout interrupted it. A terminal Ctrl-C
    also reaches EasyCrypt, and its answer can come before the flag is seen. So `stopped` is
    decided when the answer arrives (`interrupted`, not timed out, flag set).
  - New `SessionError::Stopped` is how the prover unwinds.
  - New `SessionError::GoalsLost` (see "Found on the way").
- **The prover** (`driver.rs`):
  - `stop_point()` runs before every sentence the walk sends (`send`, `admit`). When the flag is
    set, it seals the oracle once, into the new field `Prover::stopped`, and returns
    `Err(Stopped)`.
  - The interrupted sentence is answered `interrupted`. From there it is handled like any failed
    attempt, rolled back included, and the next sentence the walk would send stops it.
  - The ladder, the rung loops and the leaf-split loop all send through `send`, so they end
    there.
  - `Unresponsive` after a stop (EasyCrypt does not answer the SIGINT within 30 s) is a stop and
    not an error (§6): `session_failed`.
  - `Sealed` now carries `node` (the `N<k>`/`router` of its admits). `seal_with(open)` seals
    with a given goal count.
- **`tactics/mod.rs`:**
  - `pub enum Interrupted { NoOracleInFlight, Lockstep { oracle }, Sealed { oracle, admits,
    node } }`. Its `Display` is the report line:
    - `sealed PKENC with 5 admits at node N22`;
    - `during lockstep execution of PKENC, nothing sealed`;
    - `no oracle was in flight`.
  - `EquivalenceTactics::interrupted` holds where the run stopped, and
    `TheoremTactics::interrupted()` returns it.
  - `tactics_for_oracle` returns `OracleEnd::{Done, Stopped { sealed, at }}`.
  - `tactics_for_equivalence`:
    - `ProofFile` is now built before EasyCrypt starts.
    - The flag is checked before the session starts, after each sentence of the proof's
      opening, and before each oracle.
    - A sealed oracle is pushed and written like a finished one: report first, then `Eq_*.ec`,
      both atomic.
    - On a stop, oracles that were not reached are not listed as "no goal".
    - The final write includes the line `interrupted: <at>`, placed just before the totals.
  - `run_tactics_inner` stops after an interrupted equivalence.
- **The live page:**
  - `LiveHandle::interrupted(text)` is a third terminal state. It shows the chip
    `tactics (interrupted)` and a neutral banner `interrupted (Ctrl-C): <at>`, and the page stops
    refreshing.
  - `StepStatus::Interrupted` ("interrupted", `b-interrupted`) is new. `TimedOut` ("timed out")
    remains for `--ec-timeout`.

## Found on the way: an interrupt can cost the goals

On the first kem-dem leaf run, the seal wrote a file that **did not compile**: `sealed PKENC with
0 admits at node N23`.

Cause: in the EasyCrypt clone, `ecTerminal.ml` catches exceptions in `Json.proof ()`. A SIGINT
that lands while EasyCrypt serializes the goals therefore gives an `ok` answer with `proof: null`
and a critical message `cannot serialize the goals: Stdlib.Sys.Break`. Serializing a deep
kem-dem goal takes about 4 s, so this is a real window, for the terminal's SIGINT and for
Domino's own. The walk then saw 0 goals, left the leaf and sealed nothing.

Domino now handles it (the clone is unchanged):

- `Response::goals_lost()` (`json.rs`) detects such an answer.
- `Session` then reads the goals again with `pragma Goals:printall.`, which changes no state.
  This re-read is not an exchange, and the transcript keeps EasyCrypt's answer as it was given.
- One case is different: the sentence a stop interrupted. There, re-reading would cost another
  serialization, so the prover stops **as if the sentence had not been sent**
  (`stop_with(before)`, the goal count from before the sentence). Nothing more is sent to that
  session.
- If the re-read also loses the goals, the result is `SessionError::GoalsLost`.

## Verification

- `session::tests`, with stand-in scripts:
  - `a_stop_request_interrupts_the_running_sentence_at_once`: under 1.5 s, and `stopped = true`.
  - `the_timeout_still_interrupts_and_is_not_a_stop`.
  - `neither_an_undo_nor_a_sentence_sent_after_the_stop_is_interrupted`.
  - `goals_lost_to_an_interrupt_are_read_again`.
- `live::tests`:
  - `an_interrupted_run_says_so_and_stops_refreshing`;
  - `a_sentence_stopped_by_ctrl_c_is_interrupted_and_one_out_of_time_is_timed_out` (AC 6, both
    statuses).
- `tactics::tests::an_interrupted_report_names_what_was_sealed`: the `Display` strings, the
  report line, and `TheoremTactics::interrupted`.
- `tactics::tests::live` (real EasyCrypt, `hello-world-oracle-rename-new`). The flag is set from
  the export observer at an event:
  - `a_stop_in_the_walk_seals_the_oracle_where_it_stands_and_the_file_compiles` (AC 1, 2, 5, 6),
    stop at the first joint goal finished:
    - the other oracle is untouched;
    - the `interrupted` admits carry the node;
    - the report equals `render()`, names the oracle, the node and the admits, and its counts
      equal the file's;
    - the page shows `tactics (interrupted)`;
    - the file **compiles**.
  - `a_stop_during_lockstep_execution_keeps_the_earlier_oracles_work` (AC 3), stop when oracle 2
    starts:
    - oracle 1's script is in the file and oracle 2 is untouched;
    - the report says `during lockstep execution of …`;
    - no `proc; inline.` is sent for oracle 2.
- `crates/domino/tests/easycrypt_ctrl_c.rs` (AC 4, 7) runs the binary with a stand-in
  `ec.native` (a shell script, no real EasyCrypt) on hello-world and sends `kill -INT` to it:
  - `ctrl_c_interrupts_the_running_sentence_seals_the_oracle_and_exits_130`:
    - exit 130 in under 3 s;
    - the handler's line is on stderr;
    - the file has `+ proc; inline.` / `admit. (* domino: router open-goal; reason:
      interrupted … *)`;
    - the report and stdout have `interrupted: sealed UsefulOracle with 1 admits at node
      router`;
    - the page has the chip, and the `admit.` step is shown as "interrupted".
  - `a_second_ctrl_c_exits_130_without_waiting_for_easycrypt`: the stand-in ignores SIGINT, so
    the first press alone would wait 30 s. Exit 130 in under 2 s.
- **Manual §5/§7, kem-dem** (`kem-dem-cca-ssp`, `--proofstep 0 --oracle PKENC`, debug build).
  SIGINT went to the **process group**, as a terminal sends it, from a script that watched the
  transcript and the page:

  | phase | SIGINT at | keypress → exit | left on disk |
  |---|---|---|---|
  | lockstep (PKENC's takes 0.9 s) | 2.2 s | 0.76 s, exit 130 | every oracle `+ proc; inline. admit.`; report `interrupted: during lockstep execution of PKENC, nothing sealed` |
  | a sentence (walk at N11/N12) | 21.5 s | 0.17 s, exit 130 | PKENC's walk down to N12 + 5 `interrupted` admits at `N12`; **compiles** (4 s) |
  | a leaf split (N22, after `skip => &1 &2 hpre.`) | 197 s | 0.15 s, exit 130 | PKENC down to the leaf, 2 `domino-verified-ec-failed` + 5 `interrupted` admits at `N22`; **compiles** (5 s) |

  The leaf run shows the lost-goals case: the interrupted `rewrite … in hpre.` answered `ok`
  without goals. Before the fix, the same run gave exit 130 but a file that did not compile.
  With a re-read instead of the "as if not sent" stop, the exit took 13 s.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean.
- Full suite, `DOMINO_EASYCRYPT=easycrypt/ec.native`:
  - without `cvc5-lib`: all pass (sspverif 514 passed, 5 ignored).
  - with `--features cvc5-lib --no-fail-fast`: sspverif 583 passed, 1 failed, 6 ignored. The
    failure is the known `debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim`
    (stories 23–33). `easycrypt_ctrl_c` 2, `easycrypt_overwrite` 5, `easycrypt_progress` 1 and
    `easycrypt_tactics_writes` 2 pass.

## Deviations and notes

- **The stop seals into `Prover::stopped`, not through `Prover::checkpoint`.** The walk seals
  where it stops, which keeps the innermost node and the open blocks, and unwinds.
  `tactics_for_oracle` turns that seal into the oracle's result, and `tactics_for_equivalence`
  writes it like any finished oracle. The `write_sealed` closure is still installed only for
  `--write-granularity node`. The result is the same write, one path fewer.
- **The interrupted sentence is rolled back only when it is part of a multi-sentence attempt.**
  That is, when the attempt had accepted sentences before it. A rollback's `undo` is never
  interrupted. The seal is consistent either way.
- **EasyCrypt stays in Domino's process group**, so a terminal Ctrl-C also reaches it:
  - The running sentence is interrupted at once, even before the flag is polled.
  - After a second press, EasyCrypt stops what it was doing and exits on stdin EOF instead of
    finishing its sentence as an orphan.
  - The cost is the lost-goals case, which is handled above.
  - A narrow race is left: EasyCrypt answers the terminal's SIGINT before the handler thread
    sets the flag. That step then shows as "timed out" instead of "interrupted". The run still
    stops.
- **Oracles not reached are not in the report.** This was already the case mid-run (story 33).
  The `Lockstep` interruption names the oracle it stopped.
- **Also a stop:** a flag set between equivalences, or while the proof is being opened, gives
  `no oracle was in flight`. Its report is written, and the file is the untouched export.
- **Follow-up for the EasyCrypt clone** (story 25's branch): `Json.proof ()` could let
  `Sys.Break` through instead of nulling the goals. Domino would then see a plain
  `interrupted`.
- `rustfmt` formatted the new test file. Other hunks follow the surrounding style. The files
  are not rustfmt-clean from before this story.

## State handed to the next story

- Ctrl-C:
  - `TacticsOptions::stop` is the flag. `main.rs` sets it through `stop_on_ctrl_c` (shared with
    `debug`).
  - `Session::set_stop` and `Session::stop_requested` read it. `Prover::stop_point` checks it
    before each sentence.
  - `SessionError::Stopped` unwinds the walk, and `Prover::stopped` holds the seal.
  - `OracleEnd`/`Interrupted` (`tactics/mod.rs`) carry the result.
  - A result that is `TheoremTactics::interrupted()` exits 130.
- `SessionEvent::Answered { stopped }`, `StepStatus::Interrupted` and `RunState::Interrupted` /
  `LiveHandle::interrupted` are on the page side.
- `Response::goals_lost()`: after an interrupt, an `ok` answer can lack its goals. `Session`
  re-reads them, except for the sentence a stop interrupted.
- The story 19 (symbolic execution) collision is still open. The flag is passed at the
  `run_lockstep_command` call in `tactics_for_oracle`, which 19 rewrites.
