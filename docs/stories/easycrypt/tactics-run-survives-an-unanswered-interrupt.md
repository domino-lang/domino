# Story — A tactics run survives an unanswered interrupt

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 26 (`Session`), 33 (the seal), 34 (Ctrl-C, `Prover::stop_with`), 37 (session
record and resume).
**Blocks:** nothing. Its EasyCrypt-side counterpart is `easycrypt-never-swallows-an-interrupt.md`;
the two can land in either order.
**Naming:** this story is named, not numbered, so it cannot collide with stories written in
parallel. Refer to it by file name.

---

## 1. Why this story exists

A proof job on 4WHS proofstep 4 (`Eq_H2_1_H3_0`) ended with *EasyCrypt did not answer `…` after
being interrupted*. The cause was EasyCrypt **swallowing** the interrupt (diagnosis in
`easycrypt-never-swallows-an-interrupt.md` §1). That story fixes the swallow we found. This one
makes Domino survive an interrupt that goes unanswered for *any* reason: an unfixed binary, a
swallow the audit missed, or a prover stuck in C code.

Today Domino does three fragile things:

- it sends **one** `SIGINT` and waits `INTERRUPT_GRACE` (30 s) (`Session::exchange`,
  `src/easycrypt/session.rs:422`);
- on `SessionError::Unresponsive` outside a Ctrl-C, `tactics_for_oracle` returns the error
  (`src/easycrypt/tactics/mod.rs:1107`, `Err(e) => return Err(e.into())`), so the **whole proof
  job fails**. The per-tactic checkpoint is left on disk, and every oracle after the stuck one is
  never attempted;
- an answer from an unfixed EasyCrypt that swallowed an interrupt looks like an ordinary `error` or
  `ok`, so nobody learns that the binary is the problem.

## 2. Inherited from earlier stories

- **Story 26:** `Session::send`/`exchange`, `Session::interrupt` (one `kill -INT`),
  `INTERRUPT_GRACE`, `Wait::{TimedOut, Stopped}`, `SessionError::Unresponsive`.
- **Story 33:** `Prover::seal`, `seal_with(open)`, `AdmitReason::Interrupted`, checkpoints through
  `write_sealed`, `ProofFile::write`.
- **Story 34:** `Prover::stop_with(open)` seals once and unwinds with `SessionError::Stopped`.
  `Prover::session_failed` already turns `Unresponsive` into a stop **when a Ctrl-C was
  requested** (`src/easycrypt/tactics/driver.rs:426`). `tactics_for_oracle` maps `Stopped` to
  `OracleEnd::Stopped { sealed, at }`.
- **Story 37:** the session record. An oracle with an `interrupted` admit is not done, so the next
  proof job resumes it. In `tactics_for_equivalence`, an oracle whose goal comes up and is already
  finished is closed with `admit.` (`is_resumed`).
- `tactics_for_equivalence` opens the proof with `call_prefix`, then the base case (admitted if
  rejected), then walks oracles in goal order (`src/easycrypt/tactics/mod.rs:715–810`).
- **Glossary:** **Interrupt** (honored / swallowed / unanswered) and **Respawn** in `CONTEXT.md`.
  Note that *restart* is already taken by **Resume mode**. Do not call the respawn a restart in
  code, messages or the report.

## 3. Work to do

### 3.1 Re-send the interrupt while waiting

In `Session::exchange`, after a timeout or a stop, keep sending `SIGINT` every
`INTERRUPT_RESEND` (5 s) until an answer arrives or `INTERRUPT_GRACE` (unchanged, 30 s) runs out:
up to six signals in total. Only then is the result `Unresponsive`.

This is safe because of the **Interrupt** rule: a signal that lands after the sentence has finished,
or between sentences, is never answered. A second signal therefore never produces a second line.
With an unfixed binary there is a small window where it can (see
`easycrypt-never-swallows-an-interrupt.md` §3.4). Accept that window; §3.4 below warns about the
binary.

Count signals sent per sentence and put the count into the transcript record, e.g. an
`"interrupts": n` field present only when `n > 0`. That way the live page and anyone reading the
transcript can see how hard a sentence was to stop.

### 3.2 An unanswered interrupt seals the oracle, not the job

When a `send` in the walk ends in `Unresponsive` without a stop request:

- the walk seals the oracle where it stands, like a Ctrl-C (`stop_with(self.count())`). The goals
  are the last answered state and the script holds only accepted sentences, so the seal is
  consistent (story 34 §2 already relies on this);
- `tactics_for_oracle` returns a new end, e.g. `OracleEnd::Unanswered { sealed, at }`. It is not
  `Stopped`, because the job is not stopping;
- the oracle's result is pushed and written like any finished oracle. Its admits carry `interrupted`,
  so the session record marks it not done, and the next proof job resumes it under whatever
  **resume mode** applies.

Keep the cause distinct from Ctrl-C everywhere it is shown. The report line for the oracle and the
live page say e.g. `EasyCrypt left an interrupt unanswered at N38 (6 signals over 30 s); oracle
sealed, EasyCrypt respawned`.

### 3.3 Respawn and carry on

After an `Unanswered` end:

1. Drop the old `Session`. `Drop` already kills the child without waiting on it.
2. Start a fresh one with the same setup as the first: transcript sink (same file, appended; the
   tag says it is a respawn), observer, timeout, stop flag. Factor that setup out of
   `tactics_for_equivalence` so both use one function.
3. Re-open the proof: `call_prefix`, then the base case. If the base case was admitted before, send
   `admit.` directly; do not try it again.
4. Continue the goal loop. Every oracle already in `proof.tactics.oracles`, including the one just
   sealed, is closed with `admit.`, exactly as resumed oracles are. Its script is already in the
   file.

**Limit.** At most `MAX_RESPAWNS` (2) respawns per proof job. On the third unanswered interrupt the
job does what Ctrl-C does: it ends with the in-flight oracle sealed (`Interrupted::Sealed`). The
remaining oracles are left `pending` in the record, and the run's summary says why. A respawn that
itself fails (spawn error, `call_prefix` rejected) ends the job the same way, with the error in the
summary.

A Ctrl-C during a respawn stops the job as a Ctrl-C (`Interrupted::NoOracleInFlight`).

### 3.4 Detect a swallowed interrupt from an unfixed binary

If an answer carries a message matching `error when starting` together with `Sys.Break`, the
binary swallowed an interrupt. Print **once per run** on stderr, and put it in the run summary:

> EasyCrypt swallowed an interrupt (`<message head>`). Rebuild it from branch
> `amir/domino-easycrypt-integration` (story `easycrypt-never-swallows-an-interrupt`); until then,
> interrupted attempts can run far past their time and proof jobs may need respawns.

Do **not** rewrite the answer's status. `ok` and `error` are truthful about EasyCrypt's state: the
sentence did run to the end. Only the warning is added.

`cannot serialize the goals: Stdlib.Sys.Break` is **not** a swallow (the goal re-read already
handles it) and must not trigger the warning.

## 4. Acceptance criteria

- [ ] **Unit, with a fake EasyCrypt** (a script that reads sentences and answers JSON lines, as the
      existing session tests do, if any; otherwise add one under `testdata/`):
  - ignores the first two `SIGINT`s and answers the third. `send` returns `interrupted`, and the
    record says `"interrupts": 3`;
  - never answers. `send` returns `Unresponsive` after ~`INTERRUPT_GRACE`, having sent six signals;
  - answers the sentence just as the first `SIGINT` is sent. Exactly one answer is consumed, and
    the next sentence gets its own answer.
- [ ] **Tactics run, with the fake EasyCrypt** made to leave one sentence of oracle 2 of 3
      unanswered: the job finishes. Oracle 1 is done, oracle 2 is sealed with `interrupted` admits
      and status `interrupted` in the record, and oracle 3 is proved in the respawned session. The
      transcript shows the respawn and `admit.` for oracles 1 and 2 in the fresh session. The file
      compiles (ADR 0005 test helper).
- [ ] Three unanswered interrupts in one job: the job ends after the third, with oracles after it
      `pending` and the reason in the summary.
- [ ] Ctrl-C while respawning ends the job as a Ctrl-C.
- [ ] An answer carrying `error when starting `Z3': … Sys.Break` produces the warning once per run.
      `cannot serialize the goals: Stdlib.Sys.Break` produces none.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
# with an EasyCrypt built *before* easycrypt-never-swallows-an-interrupt:
cd example-projects/4WHS
$D easycrypt --force
$D easycrypt prove --theorem Full4WHS --proofstep 4
# expect: the swallow warning once; if an interrupt goes unanswered, a respawn line in the report
# and the job going on to the next oracle instead of failing
jq -r 'select(.interrupts) | "\(.interrupts) \(.ms) \(.sentence)"' \
  _build/easycrypt/Full4WHS/progress/Eq_H2_1_H3_0/ec-transcript.jsonl
jq '.oracles[] | {name, status}' _build/easycrypt/Full4WHS/Eq_H2_1_H3_0.session.json
```

## 6. Notes / risks

- A respawn costs the time to re-open the proof (`require`, the lemma, `call_prefix`), which is a
  few seconds on 4WHS. Measure it and put it in the report.
- The live page's transcript offsets (story 31) must survive the respawn. The sink keeps appending
  to the same file, so offsets stay valid; check that the page does not assume one EasyCrypt per
  file.
- `RUNG0_TIMEOUT` (2 s) is out of scope (owner's decision). With an unfixed binary it is the main
  source of interrupts. Record how many interrupts a 4WHS proofstep sends, as input for tuning it
  later.
- Respawning re-proves nothing *within* the job. Picking the sealed oracle back up is the next proof
  job's work, through the session record. Node-level continuation inside the job is deliberately
  not done here.

## 7. State handed on

Record in the report how many respawns and swallow warnings a full 4WHS `prove` produced, before
and after the EasyCrypt fix.
