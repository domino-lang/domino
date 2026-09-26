# Story 41 — The EasyCrypt transcript keeps only the first goal

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 31.
**Blocks:** nothing.

---

## 1. Why this story exists

The owner: *"I want to further reduce the size of progress jsonl files so only the first goal
capped to the characters is stored."*

Story 31 capped each answer to 3 goals of 12,000 characters (`GOALS_PER_STEP`, `GOAL_TEXT_CAP` in
`src/easycrypt/transcript.rs`), up to ~36 kB of goal text per sentence. With story 38 writing after
every sentence and story 36 running several jobs at once, the transcripts are the largest thing a
run leaves behind.

## 2. Inherited from earlier stories

- **Story 31:** `cap_response`, the `goals_dropped`/`text_dropped` fields, the byte-offset
  contract, `--ec-transcript full`.
- **Story 28:** the live page embeds per step exactly what a capped record holds; `GOALS_PER_STEP`
  and `GOAL_TEXT_CAP` are the contract between the two and are defined only in `transcript.rs`.

## 3. Work to do

- `GOALS_PER_STEP = 1`, `GOAL_TEXT_CAP = 2_000`. Nothing else in the record changes:
  `goals_dropped` and `text_dropped` are still always written.
- The page shows one goal per step, and says `+k goals not kept` when `goals_dropped > 0`.
- `--ec-transcript full` still writes EasyCrypt's answer verbatim; the page still embeds one capped
  goal from it.
- Update the module doc of `transcript.rs`, story 31's size figures where they are quoted as
  current, and the CLI help of `--ec-transcript`.

## 4. Acceptance criteria

- [ ] Story 31's tests updated to the new constants; a record of a 5-goal answer holds one goal and
      `goals_dropped: 4`.
- [ ] The transcript of kem-dem proofstep 0 is measured before and after; record both sizes.
- [ ] The page of that run renders one goal per step with the `+k` note.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt prove --theorem <T> --proofstep 0 -f
ls -l _build/easycrypt/<T>/progress/*/ec-transcript.jsonl
```
