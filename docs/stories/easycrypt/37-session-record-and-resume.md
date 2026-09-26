# Story 37 — A session record lets a proof job resume an equivalence

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 35 (the minimal record), 36 (one job per equivalence).
**Blocks:** 38.
**Records:** `docs/adr/0006-a-proof-job-never-translates.md`; amends ADR 0004's *Resuming is not
addressed*.

---

## 1. Why this story exists

The owner: *"If the proof contains partial proof for some oracles, we don't reprove those oracles.
Maybe we need to generate a json file for each proofstep which explains which oracles and which
nodes and smt tactics were applied in the last session so we can resume from that!"*

After story 35 a partial record makes `prove` skip the equivalence, and `-f` throws away every
oracle that was proved. A kem-dem oracle can take minutes; a stopped run should cost only the
oracle that was in flight.

## 2. Inherited from earlier stories

- **Story 35:** `Eq_<L>_<R>.session.json` with `complete` and per-oracle `status`; written after
  `Eq_*.ec` at every checkpoint.
- **Story 36:** the lock; nothing else writes the record while a job runs.
- **Story 33:** `Prover::seal`, `ProofFile::write`, `OracleTactics`, `AdmitReason`.
- **`--oracle`:** oracles not selected are closed with `+ proc; inline. admit.` in the live session
  and in the file (`selected` in `tactics_for_equivalence`).

## 3. Work to do

### 3.1 What the record holds

```json
{
  "version": 2,
  "theorem": "…", "left": "…", "right": "…",
  "domino": "<version>", "updated": "<RFC 3339>",
  "complete": false,
  "oracles": [
    {
      "name": "PKENC",
      "status": "done",
      "script": "<the oracle's bullet exactly as rendered into Eq_*.ec>",
      "admits": [{"node": "N7", "reason": "refuted"}],
      "lockstep": {"joint_paths": 23, "ms": 41200},
      "nodes": [{"id": "N0", "tactics": ["proc.", "inline.", "…"]}, {"id": "N7", "tactics": ["…"]}]
    },
    {"name": "DEC", "status": "interrupted", "nodes": [ … ]},
    {"name": "ENC", "status": "pending"}
  ]
}
```

- `script` is present only for `done` oracles and is what resuming writes back. It is the rendered
  text, so the file is rebuilt without parsing a `.ec`.
- `nodes` lists, per joint node, the sentences EasyCrypt accepted that are still in the script, in
  order. It is not used by this story; it exists so node-level resume can be added later without a
  format change. Rejected attempts are not recorded here (the transcript has them).
- A version-1 record from story 35 is read as "statuses only, no scripts": its `done` oracles cannot
  be resumed and are re-proved, with a warning saying so.

### 3.2 Deciding what to do

| Record | Without `--force` | With `--force` |
|---|---|---|
| none | prove every selected oracle | same |
| `complete` | warn, skip, exit 0 | discard, prove from scratch |
| partial | warn `resuming Eq_L_R: 2 of 5 oracles already proved`, prove the rest | discard, prove from scratch |

With `--oracle O`:
- `O` done → warn and skip; with `--force`, re-prove `O` alone and keep every other oracle's entry.
- `O` not done → prove it; other oracles keep their entries and scripts.

### 3.3 Resuming

For each oracle in goal order:
- **done:** send `admit.` for its goal in the live session (ADR 0006: not re-proved, not re-sent)
  and render its recorded `script` into the file. Its `OracleTactics` comes from the record, so the
  report counts its admits correctly.
- **interrupted** or **pending:** prove from the start, fresh lockstep execution included.

The report and the page mark resumed oracles as `resumed from session record` so they are not
mistaken for work of this run.

### 3.4 Writes

At each checkpoint: `Eq_*.ec`, then the report, then the record, each atomically (story 35 §3.4
explains the order). `complete` is true when every oracle of the equivalence is `done`, whether
this run or an earlier one proved it.

## 4. Acceptance criteria

- [ ] Ctrl-C during the third oracle of a kem-dem equivalence, then `prove` again: the first two
      oracles are not walked (no lockstep execution, no sentences but `admit.` for them in the
      transcript), the file holds their scripts byte-identical to before, and the third is proved.
- [ ] The resumed `Eq_*.ec` compiles with `easycrypt compile` (the test helper from ADR 0005).
- [ ] `complete` record → skip; `-f` → from scratch; `--oracle O -f` → only `O` re-proved.
- [ ] Killing the process with `kill -9` between the proof-file write and the record write leaves a
      state from which `prove` resumes correctly (a test that writes the file and not the record).
- [ ] A version-1 record is resumed with its done oracles re-proved and a warning.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --force
$D easycrypt prove --theorem <T> --proofstep 0      # Ctrl-C during the third oracle
$D easycrypt prove --theorem <T> --proofstep 0      # resuming … 2 of N
jq '.oracles[] | {name, status}' _build/easycrypt/<T>/Eq_*.session.json
```

## 6. Notes / risks

- A resumed file is only as good as its record. Nothing re-checks the recorded scripts (ADR 0006);
  the compile test in CI is what catches a render defect.
- Resuming after re-translating without `--force` cannot happen: translation refuses while a record
  exists, and `--force` deletes records (story 35 §3.5).
- Update ADR 0004's *Resuming is not addressed* bullet to point at this story.

## 7. State handed to the next story

Story 38 makes checkpoints happen after every accepted sentence; the record must stay cheap to
write. Record its size on kem-dem's largest equivalence.
