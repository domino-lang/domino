# Story `tactics-run-survives-an-unanswered-interrupt` — implementation report

## What changed

- **`src/easycrypt/session.rs`** (§3.1)
  - `INTERRUPT_RESEND` (5 s) next to `INTERRUPT_GRACE` (30 s, unchanged).
    `Session::interrupt_until_answered` sends `SIGINT`, then sends it again every
    `INTERRUPT_RESEND` until a line arrives or `INTERRUPT_GRACE` has passed since the first one.
    That is at most six signals. A closed output while waiting counts as unanswered, as before.
  - `SessionError::Unresponsive` now carries `signals` and `waited`. Its message ends
    `(<n> signals over <s>s)`.
  - The count of signals is passed to the transcript record and to the observer
    (`SessionEvent::Answered { interrupts }`).
  - `#[cfg(test)] Session::set_interrupt_timing(grace, resend)` lets tests shorten both times.
- **`src/easycrypt/transcript.rs`**: `record(…, interrupts, answer)` writes `"interrupts": n`
  before `"response"`, only when `n > 0`.
- **`src/easycrypt/json.rs`** (§3.4): `Response::swallowed_interrupt()` returns the head of a
  message (first line, at most 160 characters) that contains both `error when starting` and
  `Sys.Break`. `cannot serialize the goals: …Sys.Break` does not match.
- **`src/easycrypt/tactics/driver.rs`** (§3.2): `Prover::session_failed` handles
  `Unresponsive` when no stop was requested. It seals the oracle where the walk stands
  (`stop_with(self.count())`, into `Prover::stopped`) and returns the `Unresponsive` error, which
  unwinds the walk. With a stop requested, it behaves as before (a stop).
- **`src/easycrypt/tactics/mod.rs`**
  - `OracleEnd::Unanswered { sealed, unanswered }`. `tactics_for_oracle` returns it when the walk
    ends in `Unresponsive` and has sealed the oracle.
  - `pub struct Unanswered { oracle, node, signals, waited, respawn: Option<Duration> }`. Its
    `Display` gives the report and page line, e.g. `EasyCrypt left an interrupt unanswered at N0
    (6 signals over 30 s); oracle sealed, EasyCrypt respawned (proof opened again in 3.8s)`, or
    `…; oracle sealed, EasyCrypt not respawned`.
  - §3.3: the session setup is factored out of `tactics_for_equivalence` into
    `SessionSetup::start`, which both the first start and every respawn use. It sets the
    transcript sink (a `try_clone` of the job's transcript `File`, which shares its offset, so
    records are appended), the tag (`<file>`, or `<file> (respawn n)`), the live-page observer
    wrapped with the swallow watch, the timeout and the stop flag.
  - `open_proof` sends `call_prefix`, then the base case. A respawn passes
    `admitted = base_case_admitted`, which sends `admit.` directly instead of trying the base case
    again.
  - `respawn(old, …)` drops the old `Session` first, then starts a fresh one and opens the proof.
    The goal loop now closes every oracle already in `proof.tactics.oracles` with `admit.`
    (`in_file`, formerly `is_resumed`), so the oracles finished before, and the sealed one, are
    admitted in the fresh session.
  - **Limit**: `MAX_RESPAWNS = 2`. On the third unanswered interrupt there is no respawn. The job
    ends with `interrupted = Interrupted::Sealed { … }` and
    `ended_early = "EasyCrypt left 3 interrupts unanswered, and a proof job respawns it at most 2
    times"`. A respawn that fails ends the job the same way, with `respawning EasyCrypt failed:
    <error>`. A Ctrl-C before or during the respawn gives `Interrupted::NoOracleInFlight` with no
    `ended_early`, i.e. a Ctrl-C.
  - `EquivalenceTactics` gains `ended_early: Option<String>` and `unanswered: Vec<Unanswered>`.
    The report prints each `Unanswered` under its oracle. A job that ended early ends its report
    with `ended early: <where>: <why>` instead of `interrupted: <where>`.
  - `TheoremTactics` gains `swallowed_interrupt: Option<String>`, printed as `warning: …` in the
    run summary. `TheoremTactics::interrupted()` now ignores jobs that ended early. The new
    `TheoremTactics::ended_early()` reports them.
  - `run_tactics_observed` creates one `SwallowWatch` per run. It warns once on stderr (through
    `eprintln_above_bars`) with the story's text. A job that ended early does not stop the run:
    the next equivalence is a job of its own.
- **`src/easycrypt/tactics/live/`**
  - `Step::interrupts` is shown as `, N interrupt(s) to stop it` in the step's detail.
  - `LiveHandle::unanswered(&Unanswered)` puts the line on the oracle (`<p class="err">`). It also
    clears `live_steps` and `pending`: an `undo` in the fresh session counts its own depths, so
    the old session's steps must not be marked undone by it.
  - `RunState::EndedEarly` and `LiveHandle::ended_early(why)` give the chip `tactics (ended
    early)` and the banner `the proof job ended early: …`, never the Ctrl-C banner.
- **`crates/domino/src/main.rs`**: after all theorems, `prove` exits 1 when a job ended early.
  A Ctrl-C still exits 130.
- **Tests**
  - `session.rs`: `interrupt_fake` is a stand-in EasyCrypt. It ignores interrupts between
    sentences and runs a shell fragment on `slow.`.
  - `tactics/tests.rs`:
    - `FakeEasyCrypt` and the thread-local `TEST_EASYCRYPT`, read by `spawn_easycrypt` under
      `cfg(test)`.
    - `unanswering_easycrypt`, a `sh` filter in front of the real EasyCrypt. It leaves the first
      N0 sentence of chosen oracles unanswered, counting the oracles walked across respawns in a
      file.
    - The new test project `testdata/easycrypt/unanswered-interrupt/four-oracles` (`Left ~ Right`,
      four `UsefulOracle`s of one `Rand`). It proves with no admit in about 3 s.
- **Docs**:
  - the inherited facts were added to `resume-an-oracle-from-its-saved-joint-tree.md` §2;
  - `CONTEXT.md` gains **Ended early** (code review).

## Verification

Final runs, after the review fixes, with `DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`. The
EasyCrypt clone is at b2511afa, which predates `easycrypt-never-swallows-an-interrupt`.

| Binary | `cargo test --workspace` | `--features cvc5-lib` |
|---|---|---|
| lib (`sspverif`) | 587 passed, 5 ignored | 678 passed, 6 ignored |
| `debug_all_claims` | 3 | 4 |
| `easycrypt_ctrl_c` | 0 | 4 |
| `easycrypt_lockstep_progress` | 0 | 1 |
| `easycrypt_overwrite` | 6 | 6 |
| `easycrypt_progress` | 1 | 1 |
| `easycrypt_prove` | 0 | 5 |
| `easycrypt_tactics_writes` | 0 | 3 |
| `sspverif_smtlib` | 2 | 2 |

Neither final run had a failure.

The first full `cvc5-lib` run failed two of the new live tests. In
`an_unanswered_interrupt_seals_the_oracle_and_a_respawned_easycrypt_proves_the_rest` and
`the_third_unanswered_interrupt_ends_the_job_and_leaves_the_rest_pending`, the opening
`require import AllCore Distr FMap …` was interrupted: under the loaded suite it took longer than
the 2 s per-sentence timeout the tests used. They had passed when run alone. Their timeout is now
10 s; the hang is chosen by the wrapper, not by the timeout. They pass in the final run.

Acceptance criteria (§4), each with its test:

- Fake EasyCrypt, `session.rs`:
  - `the_interrupt_is_sent_again_until_it_is_answered`: answered on the 3rd signal, and the
    record has `"interrupts":3`;
  - `an_interrupt_never_answered_is_unresponsive_after_six_signals`;
  - `an_answer_that_crosses_the_first_interrupt_is_the_only_one`.
- Tactics run (`tactics::tests::live`, real EasyCrypt behind `unanswering_easycrypt`):
  - `an_unanswered_interrupt_seals_the_oracle_and_a_respawned_easycrypt_proves_the_rest`. Oracle 2
    of 4 is left unanswered. The record says Done / Interrupted / Done / Done. The `(respawn 1)`
    transcript opens the proof again and sends `admit.` for oracles 1 and 2. The file compiles.
  - `the_third_unanswered_interrupt_ends_the_job_and_leaves_the_rest_pending`. The record says
    Interrupted ×3 / Pending. The job ended early with the reason given.
  - `a_ctrl_c_while_respawning_stops_the_job_as_a_ctrl_c`, which gives `NoOracleInFlight`.
- Swallow, `tactics::tests`:
  - `a_swallowed_interrupt_is_warned_about_once_per_run`. Two swallowing answers produce one
    warning, and `cannot serialize the goals: Stdlib.Sys.Break` produces none;
  - `an_unanswered_interrupt_is_its_own_line_in_the_report`.

`cargo clippy --workspace --all-targets` (both feature sets) reports only the warnings that
predate this story: `src/debug/sweep.rs:199`, plus the `TempDir::into_path` deprecations with
`cvc5-lib`.

**Respawn cost (§6).** I measured it on a `/tmp` copy of a Full4WHS export (`Eq_H2_1_H3_0.ec`,
proofstep 4, real `ec.native`). Starting EasyCrypt took 0.32 s. Opening the proof (the 11
sentences of `call_prefix` and the base case) took 3.43 s, of which the base case
`auto => />; smt(...)` was 1.35 s. That is about **3.8 s per respawn**, or about 2.4 s when the
base case was admitted before. On the four-oracle test project a respawn takes 1.3–1.7 s.

## Deviations and notes

- **§7 counts not measured.** A full 4WHS `prove` was not run (overview §7 forbids `prove` on 4WHS
  in an agent session). The number of respawns and swallow warnings before and after the EasyCrypt
  fix, and §6's count of interrupts per proofstep, are still open. §5 is the owner's check.
- **"Proof job" is one equivalence.** A job that ended early (respawns ran out, or a respawn
  failed) does what Ctrl-C does *to that job*: in-flight oracle sealed, the rest `pending`. It does
  not stop the run: the theorem's next equivalence is a proof job of its own. A Ctrl-C still stops
  everything and exits 130. To keep the cause visible to scripts, `prove` exits **1** after the run
  when any job ended early. The story does not ask for that exit code. It is the user's call.
- **The acceptance test uses oracle 2 of 4**, not 2 of 3. The project has four oracles so that the
  three-respawns test has a `pending` oracle after the third.
- **Only the walk handles `Unresponsive`** (§3.2 "a `send` in the walk"). An unanswered interrupt
  outside it still fails the job, as before:
  - opening the proof in the first session;
  - the goal loop's `admit.` for finished oracles (also in a respawned session);
  - the `admit.` after a failed lockstep execution.

  None of these are interrupted on a timeout in practice, since they take milliseconds.
- **No transcript record for the unanswered sentence.** It has no answer, and a record is
  "sentence + answer", so the six signals appear in the report line and on the live page, not as an
  `"interrupts"` record. Every *answered* sentence that needed an interrupt carries its count.
- **"Once per run" is once per `run_tactics_observed`**, i.e. per theorem. That is no more often
  than once per tactics run (one proof job, `CONTEXT.md`). `prove` over several theorems can warn
  once per theorem.
- **An `Unresponsive` during an `undo`** (rolling back an abandoned attempt) seals the oracle as it
  stands, before the script is rolled back. The script then keeps the abandoned attempt's accepted
  sentences and admits the goals of the last answer. EasyCrypt accepts that, as for any seal, but
  no test compiles a file sealed at exactly that point.
- **A closed EasyCrypt output during the grace is `Unresponsive`**, as before: it did not answer
  either.
- **Ctrl-C while respawning.** The test stops before the fresh EasyCrypt starts. A stop *while* the
  proof is being opened again reuses `open_proof`'s stop checks, the same ones the first opening
  uses, and gives `NoOracleInFlight` too. That path has no test of its own.

## Code review

The `code-review` skill ran against d2600bf7 with two sub-agents. The spec was the story file,
with overview §6–7 and `CONTEXT.md` for context. `docs/agents/issue-tracker.md` is missing: the
skill says to run `/setup-matt-pocock-skills`.

**Standards** (no hard violations; judgement calls):

- *"Ended early" is a new domain concept missing from `CONTEXT.md`*: fixed, the entry was added.
- *Nested tuple `Some((signals, waited))` in `tactics_for_oracle`* (user preference: named
  structs): fixed. The `Unanswered` struct is built where the error is matched.
- *`swallow_warning` hard-codes the branch name*: fixed. It uses `session::JSON_BRANCH`, now
  `pub(crate)`.
- *Durations formatted inconsistently*: `Unresponsive` now says `over N s`, like the report line.
- *Magic number 160*: now a named constant.
- Kept, recorded under follow-up:
  - the `(line, timed_out, interrupts)` and `(result, stopped, unanswered)` tuples, which are
    local destructurings;
  - an enum for how a job ended, to replace the `interrupted` + `ended_early` pair that is matched
    in four places;
  - `Prover::stopped` now also holds an unanswered seal;
  - `respawn` edits `EquivalenceTactics` (feature envy);
  - `open_proof`'s `admitted` flag;
  - the `#[cfg(test)]` thread-local seam in `spawn_easycrypt`;
  - the duplicated count of `interrupted` admits;
  - the duplicated flush-and-exit in `main`.

**Spec** (§3.1–3.4 present; resend timing, respawn, limit, record statuses and the swallow rule
judged correct; live-page offsets survive a respawn):

- *Once per run vs. per theorem*, *no record for the unanswered sentence*, *Ctrl-C during the
  re-open untested*, *`Unresponsive` outside the walk*, *seal during an `undo`*: kept. All are
  recorded above as deviations.
- *Exit 1 and later equivalences going on*: kept, flagged above for the user.
- *`live.unanswered` clears `live_steps` after the fresh session's opening steps are pushed*: kept.
  It is harmless, since the walk never undoes into the opening.
- *The new section in the resume story*: kept (task step 3).

## State handed to the next story

- `Session::exchange` re-sends `SIGINT` every `INTERRUPT_RESEND` (5 s) within
  `INTERRUPT_GRACE` (30 s). `SessionError::Unresponsive { sentence, signals, waited }`.
- Transcript records carry `"interrupts": n` (n > 0). After a respawn, records are tagged
  `<file> (respawn n)` and `state` numbers start again in each session.
- An unanswered interrupt in the walk ends the oracle as `OracleEnd::Unanswered`. Its result is
  written like a Ctrl-C seal (admits `interrupted`, record status `interrupted`), so the next proof
  job resumes it under its resume mode.
- In the goal loop, every oracle already in `proof.tactics.oracles` gets `admit.` (`in_file`). The
  resume story must keep that rule for the oracles it re-walks in a respawned session. A trust or
  replay re-walk interrupted by an unanswered interrupt is sealed by the same `stop_with` path.
- `MAX_RESPAWNS = 2` per proof job. Afterwards `EquivalenceTactics::ended_early` gives the reason.
  `TheoremTactics::interrupted()` ignores such jobs; `TheoremTactics::ended_early()` reports them.
- `SessionSetup::start` is the one place a session of a proof job is set up, and `open_proof` the
  one place the proof is opened.
- `LiveHandle::unanswered` clears the live steps; `LiveHandle::ended_early` sets the run state.

## Notes for follow-up

- Owner checks (§5, §7): run `prove --theorem Full4WHS --proofstep 4` with the old and the fixed
  EasyCrypt. Record the respawns, swallow warnings and interrupts sent (`jq 'select(.interrupts)'`
  on the transcript).
- Handle `Unresponsive` on the goal loop's `admit.` sends in a respawned session as "a respawn that
  fails": end the job instead of failing the run.
- One refactor for the Standards smells kept above:
  - an enum for how a job ended (done / stopped / ended early);
  - rename `Prover::stopped` (it holds any seal);
  - move `respawn` onto `EquivalenceTactics`;
  - an `OracleStats::interrupted_admits()`;
  - pass the test EasyCrypt through `SessionSetup` instead of a thread-local.
- Pre-existing: `src/debug/sweep.rs:199` (clippy `collapsible_if`) and the `TempDir::into_path`
  deprecations.
