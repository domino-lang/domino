# Story 34 — Ctrl-C stops a tactics run and leaves a partial proof

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 33 (the seal — this story has nothing to produce without it), 27, 28.
**Blocks:** nothing.
**Conflicts with:** `docs/stories/symbolic-execution/19-all-claim-runs-and-strategy-split.md`,
which rewrites the `run_lockstep_command` call this story threads a stop flag through. Whichever
lands second adjusts. See §6.

---

## 1. Why this story exists

The owner, on what a stopped run should leave behind: *"when the process is stopped when ctrl+c,
then it should contain the partial proof plus admits for the remaining goals. Otherwise, it is as
much as proof written there."*

Story 33 gives the second half: whatever the last incremental write left is on disk, under every
kind of stop. This story gives the first half — a deliberate Ctrl-C produces a **partial proof** of
the oracle in flight, sealed at the node the walk had reached, rather than losing it back to the
last write.

There is no signal handling in the `easycrypt` path at all today. `ctrlc::try_set_handler` is
installed only by `debug()` (`crates/domino/src/main.rs`), and `ctrlc` is already a dependency of
`crates/domino`. So Ctrl-C during a tactics run kills the process outright.

## 2. Inherited from earlier stories

- **Story 33:** the seal, `--write-granularity`, `AdmitReason::Interrupted`.
- **Story 26:** `Session::interrupt` — SIGINT to the EasyCrypt child, after which the running
  sentence is answered `Status::Interrupted`; `INTERRUPT_GRACE` (30 s) bounds the wait for that
  answer. `Session::undo_to`.
- **Story 28:** `LiveHandle::finish` and `fail`; the page's step statuses, where
  `Status::Interrupted` currently maps to `StepStatus::TimedOut`
  (`src/easycrypt/tactics/live/mod.rs`).
- **`domino debug`'s handler** (`crates/domino/src/main.rs`) is the pattern to follow: first press
  sets a flag and prints what it will do, second press exits 130. `run_lockstep_command` already
  takes `stop: Option<&AtomicBool>` — the tactics path passes `None`.

## 3. Work to do

### 3.1 The handler

As in `debug()`: first press sets an `AtomicBool` and prints one line saying what will happen;
second press exits 130 immediately. If a handler is already installed, the run is simply not
interruptible — not fatal.

### 3.2 Where the stop takes effect

A sentence can run to `--ec-timeout` (60 s default) and a leaf split to `--leaf-budget` (300 s
default), so a flag checked only between sentences means up to a minute of apparent deadness after
you pressed the key. Instead:

1. **SIGINT the EasyCrypt child** via `Session::interrupt`, so the running sentence is answered
   `interrupted` at once. The prover treats that exactly as it treats any failed attempt — roll the
   node back — rather than as an error.
2. **Break the rung ladder and the leaf-split loop**, so the walk does not spend another 4–5 s per
   `smt()` trying the next rung on the way out.
3. **Pass the stop flag into `run_lockstep_command`.** Lockstep execution runs first for every
   oracle and is where the time goes on a large one; passing `None` there means the key does nothing
   during the slowest phase. `domino debug` already does this, including the caveat that the
   in-flight cvc5 query is an uncancellable FFI call.

### 3.3 What it leaves

- The oracle in flight is **sealed** (story 33 §3.1) and written, with its remaining goals labelled
  `interrupted`.
- Oracles already finished keep their scripts; oracles not reached keep
  `+ proc; inline. admit.`.
- The report is rewritten to match (story 33 §3.3), with a line naming what was sealed:
  `interrupted: sealed <oracle> with N admits at node N<k>`.
- The theorem-level summary still prints.
- **Exit 130.** A partial proof is not a success, and 130 is what `debug`'s second press already
  returns, so the two commands agree.

### 3.4 The page says "interrupted", not "failed"

`Live` gets a third terminal state beside `finish` and `fail`: an `interrupted` chip. Nothing went
wrong, so `fail` is the wrong signal.

Separately, split the step status: `Status::Interrupted` currently renders as "timed out", which
conflates the `--ec-timeout` case with a deliberate Ctrl-C. Once §3.2 starts producing interrupts on
purpose, your own keypress would read as a timeout. Two statuses: **timed out** (the timeout) and
**interrupted** (you).

### 3.5 Ctrl-C outside the walk

During the export itself, leave it alone: it is seconds long and holds nothing on disk yet.

## 4. Acceptance criteria

- [ ] Ctrl-C during a kem-dem `--tactics` run on `PKENC` exits 130 within a couple of seconds, and
      `Eq_*.ec` holds `PKENC`'s proved bullets plus `interrupted` admits and compiles.
- [ ] Oracles finished before the press keep their full scripts; oracles not reached keep the
      unlabelled `+ proc; inline. admit.`.
- [ ] Ctrl-C during lockstep execution (before any sentence is sent) stops the run and leaves the
      earlier oracles' work, exit 130.
- [ ] Second press exits 130 immediately, without waiting for the in-flight sentence.
- [ ] The report names the sealed oracle and node, and its admit counts match the file.
- [ ] The final page shows an `interrupted` chip, not `failed`, and the interrupted sentence shows
      as "interrupted", while a genuine `--ec-timeout` expiry still shows as "timed out". Cover
      both.
- [ ] A test with a stand-in `easycrypt` script (as story 28's tick test does, so no real EasyCrypt
      is needed) drives the handler path end to end.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh; export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --tactics --proofstep 0            # Ctrl-C during PKENC
echo $?                                          # 130
grep -c 'reason: interrupted' _build/easycrypt/*/Eq_*.ec
easycrypt compile -I _build/easycrypt/<theorem> _build/easycrypt/<theorem>/Eq_*.ec
open _build/easycrypt/*/progress/index.html      # interrupted chip
```

## 6. Notes / risks

- **The story 19 collision.** `docs/stories/symbolic-execution/19-…` (untracked, unimplemented)
  moves EasyCrypt debugging to `domino easycrypt --debug` and relocates lockstep artifacts to
  `<out>/<theorem>/!debug!/`. It rewrites the very call site §3.2's third point threads a flag
  through. This story is sequenced last partly for that reason; if 19 lands first, thread the flag
  through its shape instead.
- `INTERRUPT_GRACE` is 30 s. If EasyCrypt does not answer the SIGINT within it, `Session` reports
  `Unresponsive`; treat that as "seal with what we have and exit 130", not as an error.
- A seal after an interrupt must not send anything to a session that is being torn down — which is
  already guaranteed by story 33 §3.1 making the seal local.
- 4WHS and yao stay off-limits for `--tactics` (overview §7).

## 7. State handed to the next story

Record in the report: what a Ctrl-C at each phase (lockstep, a sentence, a leaf split) actually
leaves on disk, measured on kem-dem, and the observed time from keypress to exit.
