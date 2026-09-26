# Story 38 — `--write-granularity tactic`, and it is the default

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 33, 37.
**Blocks:** nothing.

---

## 1. Why this story exists

The owner: *"I want every tactic that is tried is also written to the file. So
--write-granularity accepts tactic as well in addition to oracle and node … make tactic the
default."*

Today the proof file is rewritten per oracle (`oracle`) or also after each joint node (`node`,
story 33). A node can take minutes on kem-dem, so `kill -9` or a crash inside one loses all of it.

## 2. Inherited from earlier stories

- **Story 33:** `WriteGranularity`, `Prover::checkpoint` (the `write_sealed` closure in
  `tactics_for_oracle`), called by `prove_node` after each node under `node`.
- **Story 37:** the session record is written after the proof file at every checkpoint.
- **ADR 0005:** writes are cheap because nothing compiles the file.

## 3. Work to do

- `WriteGranularity::Tactic`, CLI value `tactic`, the **default** of `domino easycrypt prove`.
- Under `tactic`, `Prover::send` calls `self.checkpoint()` after every sentence EasyCrypt
  **accepts**. The file is sealed at each write, so it stays a proof EasyCrypt accepts. A sentence
  that is accepted and later undone (a rung that does not close its goal) is in one write and gone
  from the next; that is fine.
- Rejected, timed-out and interrupted sentences never trigger a write and never enter the file. They
  are in the transcript.
- `node` and `oracle` keep their meaning.
- Update the CLI help of `--write-granularity`.

## 4. Acceptance criteria

- [ ] `prove` on a kem-dem equivalence with no flag writes after each accepted sentence: a test with
      the stand-in `easycrypt` of story 28 counts writes equal to accepted sentences (plus the
      oracle-end writes).
- [ ] `kill -9` at a random moment of a kem-dem run leaves an `Eq_*.ec` that compiles and a session
      record from which story 37 resumes.
- [ ] The run time of kem-dem proofstep 0 under `tactic` is within 5% of `node`; record both.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt prove --theorem <T> --proofstep 0 &
sleep 60; kill -9 %1
easycrypt compile -I _build/easycrypt/<T> _build/easycrypt/<T>/Eq_*.ec
$D easycrypt prove --theorem <T> --proofstep 0     # resumes
```

## 6. Notes / risks

- If the 5% bound fails on a large equivalence, the cost is the rendering and the record's
  serialisation, not the disk; profile before changing the default back.
