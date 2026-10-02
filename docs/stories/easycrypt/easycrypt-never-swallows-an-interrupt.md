# Story — EasyCrypt never swallows an interrupt

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 "EasyCrypt
interaction", §8.1b).
**Repository:** the EasyCrypt clone at `easycrypt/`, which is its own git repository, **branch
`amir/domino-easycrypt-integration`** (story 25's branch). Nothing in this story is committed to
Domino except its implementation report under `docs/stories/easycrypt/`.
**Depends on:** 25 (`cli -json`).
**Blocks:** nothing. `tactics-run-survives-an-unanswered-interrupt.md` is its Domino-side
counterpart; the two can land in either order.
**Naming:** this story is named, not numbered, so it cannot collide with stories written in
parallel. Refer to it by file name.

---

## 1. Why this story exists

The owner keeps seeing a proof job end with *EasyCrypt did not answer `…` after being interrupted*
(`SessionError::Unresponsive`, `src/easycrypt/session.rs:69`). `Eq_H2_1_H3_0.ec` of 4WHS
(`Full4WHS`, proofstep 4) was the reported case. The diagnosis (2026-09-27, from that run's
`ec-transcript.jsonl`):

1. Domino sends one `SIGINT` when a sentence runs past its time (`--ec-timeout`, 60 s, or 2 s for
   the first `auto => /#.` attempt, `RUNG0_TIMEOUT`), then waits `INTERRUPT_GRACE` (30 s) for the
   answer.
2. On 4WHS goals most of an `smt` call's time is spent in Why3's transformations and printing,
   because the goals repeat a sixteen-field game-state record literal many times. That work runs
   once per prover, inside `run_prover` (`easycrypt/src/ecProvers.ml`), which ends in a catch-all:
   ```ocaml
   with e ->
     notify `Warning "error when starting `%s': %a" ...; None
   ```
   The catch-all also catches `Sys.Break`, either bare or wrapped by Why3 as
   `Trans.TransFailure (name, Sys.Break)` (`why3/src/core/trans.ml:366` wraps every exception a
   transformation raises). The interrupt is turned into a warning, one prover is dropped, and the
   sentence carries on.
3. When what is left of the sentence takes longer than 30 s, Domino gives up and the proof job fails.

Evidence from the two transcripts of that run (the `_build` tree has since been removed; §5 says
how to reproduce):

| | `Eq_H1_1_H2_0` | `Eq_H2_1_H3_0` |
|---|---|---|
| interrupts honored (answer `interrupted`) | many, ~4 s for a 2 s attempt | many, 3.8–5.0 s |
| interrupts swallowed (`error when starting … Sys.Break`) | ~19, 6.0–16.3 s | 7, 5.8–10.8 s |
| `cannot serialize the goals: Stdlib.Sys.Break` | 3 | 0 |
| unanswered (job failed) | — | 1, the sentence after record 257 (`sp.`, N38 of `Send2`) |

Example message on a swallowed interrupt:
`error when starting `Z3': Failure in transformation eliminate_builtin anomaly: Stdlib.Sys.Break`.

A swallowed interrupt that does not end in a failure is still costly: a 2 s attempt runs 6–16 s,
and its answer is `error`, not `interrupted`, so the attempt reads as "tactic failed" when it was
really "ran out of time".

## 2. Inherited from earlier stories

- **Story 25:** `cli -json`, the `from_json` terminal (`easycrypt/src/ecTerminal.ml`), its contract
  of exactly one JSON line per sentence, and its rule that an interrupt arriving while EasyCrypt
  waits for the next sentence is not answered (`finish` drops `ST_Failure` of an interrupt while
  `idle`). `Sys.catch_break true` is set because the terminal is interactive (`ec.ml`).
- `EcScope.toperror_of_exn_r` maps `Sys.Break` to `HiScopeError (None, "interrupted")`, which
  `Json.is_interrupt` recognises.
- **Domino side (unchanged by this story):** `Session::exchange` sends `SIGINT` on timeout or stop
  and waits `INTERRUPT_GRACE`. An answer whose goals are missing (`Response::goals_lost`) is
  followed by a goal re-read with `pragma Goals:printall.`.

## 3. Work to do

### 3.1 Interrupts pass through `run_prover`

- Add one predicate, e.g. `EcUtils.is_interrupt : exn -> bool` or a local helper in
  `ecProvers.ml`. It is true for `Sys.Break` and for any wrapper whose payload is an interrupt;
  `Why3.Trans.TransFailure (_, e)` is the one confirmed. Unwrap recursively.
- `run_prover`'s handler becomes `with e when not (is_interrupt e) -> …`. An interrupt re-raises
  as `Sys.Break` itself, not wrapped, so `toperror_of_exn_r` maps it to `interrupted`.
- `execute_task`'s `try_finally` clean-up already kills and waits for the provers started so far.
  Check that this holds when the interrupt escapes from the *second or later* `run` (the first
  prover is already running).

### 3.2 Audit the `smt` path for other swallows

Go through every `with e ->`, `with _ ->` and `try … with` on the path from the `smt` tactic to the
provers: `ecProvers.ml` and `ecSmt.ml`, plus anything they call that runs while a prover is being
prepared or awaited. For each, record in the implementation report one of: *cannot see an
interrupt*, *fixed with `is_interrupt`*, or *deliberately kept* (with why). Do not widen the audit
to all of EasyCrypt; this is about the code where the time goes.

### 3.3 No ignored-`SIGINT` window in the parent

`maybe_start_why3_server` sets `SIGINT` to *ignore* around every call, so an interrupt landing in
that window is dropped entirely. The ignore exists so that the forked `why3server` does not die on
a terminal Ctrl-C. It only matters for the child, and the server is only started when
`Prove_client.is_connected ()` is false, which is once per process.

- Set `SIGINT` to ignore **in the child**, after `Unix.fork` and before `exec`. Leave the parent's
  disposition untouched.
- If that is not possible on some path (e.g. an external server), at least narrow the window to the
  first start and say so in the report.

### 3.4 Exactly one answer per sentence, wherever an interrupt lands

Story 25's contract is one line per sentence. Two windows can break it today:

- **Before the parse.** `from_json#next` sets `idle <- true` only after `EcIo.drain`. An interrupt
  during `drain` reaches `finish` with `idle = false` and is answered, even though no sentence was
  sent. `idle` must cover the whole wait for the next sentence, drain included.
- **While answering.** An interrupt raised inside `answer`, during goal serialisation, the message
  flush or the output, escapes to `ec.ml`'s outer handler, which calls `finish (ST_Failure …)`
  again. That writes a second line, possibly after half of the first. While a sentence is being
  answered, an interrupt must be held back. The sentence has already finished, so the interrupt
  then changes nothing (see **Interrupt** in `CONTEXT.md`). One way: swap in a `SIGINT` handler that
  only records the signal for the duration of `answer`, restore `Sys.catch_break true` afterwards,
  and drop the recorded signal.

A side effect: `Json.proof` can no longer be interrupted, so `cannot serialize the goals:
Stdlib.Sys.Break` stops occurring. Keep `Json.proof`'s own catch-all for genuine serialisation
failures. Domino keeps its goal re-read for older binaries.

### 3.5 Format

Nothing in `doc/json-output.md`'s format changes, and the version stays `domino-json/1`. Add a short
"Interrupts" paragraph to that document saying the three guarantees: an interrupt during a sentence
ends it `interrupted`; one that arrives after it finished or between sentences is never answered;
there is never more than one line per sentence.

## 4. Acceptance criteria

- [ ] A test in the clone's test suite, or a script under `easycrypt/scripts/` that the report
      names, runs `cli -json` on a goal whose `smt` takes several seconds in Why3's transformations,
      sends `SIGINT` repeatedly at random offsets (≥ 50 trials), and checks for every trial: exactly
      one answer line; status `interrupted` or (if the signal came after the sentence finished) the
      normal answer; no message containing `Sys.Break`; the session still answers the next
      sentence.
- [ ] The same harness with the signal sent between sentences, and while a large goal is being
      printed, gets no extra line.
- [ ] A terminal Ctrl-C still does not kill `why3server` (start an `smt`, interrupt, run another
      `smt`; it uses the same server).
- [ ] Re-run 4WHS `prove` on proofstep 4 (H2_1 ~ H3_0) with the fixed binary. The transcript has no
      `error when starting … Sys.Break` message. 2 s attempts that are interrupted answer
      `interrupted`, and the report gives their median and max time next to this story's baseline
      (§1). The run does not end in `Unresponsive`.
- [ ] `make` (or the clone's usual build) and its existing test suite pass.

## 5. How to verify

```bash
cd easycrypt && git checkout amir/domino-easycrypt-integration && make
export DOMINO_EASYCRYPT=$PWD/ec.native
cd ../example-projects/4WHS
$D easycrypt --force
$D easycrypt prove --theorem Full4WHS --proofstep 4
T=_build/easycrypt/Full4WHS/progress/Eq_H2_1_H3_0/ec-transcript.jsonl
jq -r 'select(.response.messages[]?.text | test("Sys.Break")) | .sentence' $T   # expect nothing
jq -r 'select(.response.status=="interrupted") | .ms' $T | sort -n              # ~2–4 s
```

## 6. Notes / risks

- OCaml delivers signals at poll points. In OCaml 5, a long C call or a tight non-allocating loop in
  Why3 can delay `Sys.Break`. That delays the answer but does not lose it; record any delay over a
  few seconds that shows up.
- Why3 may wrap exceptions in more than `TransFailure`, e.g. printer or driver errors. The audit
  (§3.2) is what finds them. A wrapper missed there shows up as a `Sys.Break` message in the §4
  harness.
- Upstreaming: the `run_prover` and `why3server` fixes are worth offering to EasyCrypt upstream
  separately from `cli -json`. Note it in the report, but do not do it as part of this story.

## 7. State handed on

`tactics-run-survives-an-unanswered-interrupt.md` warns when it sees a swallowed interrupt from an
unfixed binary. Name the commit of this story in its report so that warning can cite it.
