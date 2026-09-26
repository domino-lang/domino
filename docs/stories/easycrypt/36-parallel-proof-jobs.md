# Story 36 — Proof jobs on different equivalences run in parallel

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35.
**Blocks:** 37.
**Records:** `docs/adr/0006-a-proof-job-never-translates.md`.

---

## 1. Why this story exists

After story 35 a proof job no longer rewrites translation's files, but its **run artifacts** are
still per theorem: `progress/index.html`, `progress/ec-transcript.jsonl` (created with
`File::create` at the start of every run, `run_tactics_inner` in `src/easycrypt/tactics/mod.rs`),
and `progress/` as the temporary directory for atomic writes. Two jobs started at once truncate each
other's transcript and overwrite each other's page. Nothing stops two jobs on the *same*
equivalence either, and those would rewrite the same `Eq_*.ec`.

The owner, on the progress files: *"let's have a different progress file for each proofstep."*

## 2. Inherited from earlier stories

- **Story 35:** `domino easycrypt prove`, the session record, the create-if-absent helper.
- **Story 28:** `LiveHandle`, `LiveConfig { page, transcript, phases, progress }`.
- **Story 31:** the transcript's byte-offset contract: the page reads goal text back by offset, so a
  transcript is never rewritten.
- **ADR 0004:** everything under `progress/` is a run artifact.

## 3. Work to do

### 3.1 One progress folder per equivalence

```
<out>/<theorem>/progress/Eq_<L>_<R>/index.html
<out>/<theorem>/progress/Eq_<L>_<R>/ec-transcript.jsonl
<out>/<theorem>/progress/Eq_<L>_<R>/lock
```

Named by equivalence, not by proofstep index, so it matches the proof file and does not move when
proofsteps are reordered. `prove` without `--proofstep` runs several equivalences in sequence, each
with its own folder, page and transcript.

There is **no** theorem-level page: it would be one file every parallel job writes to. The
`transform`/`types`/… phases the page used to show from the export are replaced by one line saying
which translation files were trusted and which were created (story 35 §3.3).

Every temporary file for an atomic write (`write_atomically`'s `tmp_dir`, the page's
`index.html.tmp`) lives in the job's own folder.

### 3.2 The lock

- Before anything else, the job creates `progress/Eq_<L>_<R>/lock` with the create-if-absent
  helper, holding its pid and start time.
- If the lock exists and its pid is alive (`kill(pid, 0)`), refuse:
  `Eq_L_R is being proved by pid 4711 (since 14:02); wait for it or stop it`. Exit non-zero.
- If the pid is dead, the lock is stale (a `kill -9`, a crash): take it over silently.
- The lock is removed on every exit the process controls: success, error, skip, both Ctrl-C paths.
- `prove` without `--proofstep` takes and releases the lock per equivalence, not for all of them at
  once, so a parallel job on a later equivalence is not blocked for the whole run.

### 3.3 Translation versus live jobs

`domino easycrypt --force` while a proof job is running would replace files under it. Translation
refuses, **even with `--force`**, if any `progress/*/lock` names a live pid, listing them. Stale
locks are ignored.

### 3.4 What is already safe

The `!debug!/<L>-<R>/` lockstep output is already split by equivalence, and `Eq_*.report.txt` is per
equivalence. Check that nothing else under the theorem directory is written by a proof job; list
anything found in the report.

## 4. Acceptance criteria

- [ ] Two `prove` processes on two different equivalences of kem-dem, started together, both finish;
      each `Eq_*.ec` holds its own proof, and each folder holds a page and a transcript whose
      records name only its own equivalence.
- [ ] A second `prove` on the same equivalence while the first runs is refused with the pid; after
      `kill -9` of the first, a new `prove` takes over the lock.
- [ ] The lock is gone after success, after an error and after Ctrl-C.
- [ ] `domino easycrypt --force` is refused while a job holds a live lock.
- [ ] A unit test for the lock: live pid refuses, dead pid is taken over.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --force
$D easycrypt prove --theorem <T> --proofstep 0 &
$D easycrypt prove --theorem <T> --proofstep 1 &
$D easycrypt prove --theorem <T> --proofstep 0      # refused: being proved by pid …
wait; ls _build/easycrypt/<T>/progress/
```

## 6. Notes / risks

- Two jobs are two EasyCrypt processes and two cvc5s, so memory is the practical limit. Record the
  peak memory of two parallel kem-dem jobs in the report.
- pid reuse can make a stale lock look live. The start time in the lock is there to show to the
  user; do not try to be clever about it.
- `check-alignment` still writes one `alignment.txt` per theorem and is not made parallel-safe here.

## 7. State handed to the next story

The per-equivalence folder and lock are in place; story 37 relies on "one job per equivalence at a
time" to read and write the session record without further locking.
