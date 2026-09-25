# Story 31 — The EasyCrypt transcript is bounded

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (`--tactics`, the transcript), 28 (the live page's embedding rule).
**Blocks:** 33 (its verification runs `--tactics` on kem-dem repeatedly).

---

## 1. Why this story exists

The owner: *"apparently the transcript record can take a lot of disk."*

It does. `_build/easycrypt/<theorem>/progress/ec-transcript.jsonl` holds one record per sentence
sent, and each record embeds EasyCrypt's answer verbatim — which prints **every open goal** as
JSON, 100–700 kB each. Story 27 measured **549 MB** for the whole kem-dem theorem; story 28
measured 4.06 MB for `PKGEN` alone, and could not run `PKENC` at all because "the disk had 2 GiB
free". Story 27's own report records the end state: *"the machine this ran on hit 'No space left on
device' once, which `--tactics` turned into an `io error talking to EasyCrypt`"* — a twelve-minute
run lost to a misleading error.

This story is first in its group because it is the precondition for developing story 33. Story 33
is verified by running `--tactics` on kem-dem's long oracles repeatedly, which is not possible at
half a gigabyte per run.

The transcript is not merely a debugging aid, which is why it cannot simply be switched off: the
live page reads goal text back out of it by byte offset (§2).

## 2. Inherited from earlier stories

- **Story 27:** the sink. `Session::set_transcript_sink` and the record written in `Session::send`
  (`src/easycrypt/session.rs`): `{"file", "ctx", "sentence", "ms", "response"}`, where `response`
  is `line.raw.trim_end()` — EasyCrypt's answer, untouched. `Session` deliberately keeps only the
  **newest** answer's goals in memory (`previous.response.proof = None`), so the transcript is the
  only place older goals exist.
- **Story 28:** the embedding rule. `Live` stores each step's `(offset, len)` into the transcript
  and `read_goal_texts` seeks to that offset to render goal text on demand. Each shown step embeds
  at most `GOALS_PER_STEP` = 3 goals, each cut at `GOAL_TEXT_CAP` = 12 000 characters
  (`src/easycrypt/tactics/live/mod.rs`). `SessionEvent::Answered` carries `record_bytes` so the
  page can count offsets.

**The constraint that decides this story:** those offsets are byte offsets into the file as
written. Anything that rewrites, compacts, reorders or compresses the transcript after the fact
invalidates every offset `Live` holds.

## 3. Work to do

### 3.1 Cap each record as it is written

`Session::send` caps the `response` it writes: at most `GOALS_PER_STEP` goals, each `pp` cut at
`GOAL_TEXT_CAP` characters, with the cut recording how many characters and how many goals were
dropped. `status`, `state`, messages and errors are kept whole — they are small and the page shows
them all.

This is **lossless for the page**: the page already cuts to exactly these limits, so a capped
record renders identically to a full one. It is also the only bounding scheme that leaves the
offsets valid, because the record is born small rather than shrunk later.

Expected effect: ~36 kB per record instead of 100–700 kB, so roughly 15–30 MB for the kem-dem
theorem against the measured 549 MB.

### 3.2 `--ec-transcript <capped|full>`

Default `capped`. `full` restores story 27's verbatim record, for the case the capped goal text cut
away the thing you wanted to read. The flag is named after the artifact (`ec-transcript.jsonl`) and
deliberately **not** `--transcript`: `domino debug` and `domino prove` already use that word for the
*solver* transcript, a different artifact (`CONTEXT.md`, "EasyCrypt transcript" vs "solver
transcript").

### 3.3 A failed transcript write must not cost a proof

Today `sink.writer.write_all(…)?` propagates an `io::Error` out of `Session::send`, which is how a
full disk became `io error talking to EasyCrypt`. Instead:

- under `capped`: drop the sink, warn once on stderr naming the path and the cause, and carry on
  proving. Steps written after the drop record no offset, and the page says "goal text not
  embedded" for them, as it already does for steps it chose not to embed.
- under `full`: fatal, with a diagnostic naming the path. The owner asked for the full log
  explicitly; failing to produce it is a real failure.

### 3.4 The page follows

`Live` tolerates steps with no transcript record (§3.3) and keeps rendering. Nothing else about the
page changes: the capped record satisfies its embedding rule exactly.

## 4. Acceptance criteria

- [ ] A unit test on the sink: a response with 10 goals of 50 000 characters each is written as a
      record holding 3 goals of at most 12 000 characters, with the cut counts stated, and with
      `status`, `state` and messages intact.
- [ ] `--ec-transcript full` writes the story-27 record byte for byte (test against a recorded
      response fixture).
- [ ] The page is unchanged by the cap: a hello-world run under `capped` and under `full` produces
      the same `strip_timings(index.html)`.
- [ ] Sink failure under `capped` does not fail the run: inject a writer that errors after N
      records, assert the run completes, one warning is emitted, and the page renders.
- [ ] Sink failure under `full` fails the run with a diagnostic naming the path.
- [ ] Measured: the transcript size of a kem-dem `--oracle PKGEN` run under both modes, recorded in
      the implementation report next to story 28's 4.06 MB.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh; export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --tactics --proofstep 0 --oracle PKGEN
ls -l _build/easycrypt/*/progress/ec-transcript.jsonl        # expect well under 4 MB
$D easycrypt --tactics --proofstep 0 --oracle PKGEN --ec-transcript full --force
ls -l _build/easycrypt/*/progress/ec-transcript.jsonl        # expect story 28's 4.06 MB
```

(`--force` is story 32; before it lands, remove the output directory between runs.)

## 6. Notes / risks

- **Do not gzip, rotate or compact.** Each breaks the byte offsets `Live` stores. If the capped
  size is ever still too large, cap harder — do not post-process the file.
- `GOALS_PER_STEP` and `GOAL_TEXT_CAP` become a contract between the sink and the page rather than
  page-local constants. Keep them in one place and say so where they are defined.
- 4WHS and yao remain off-limits for `--tactics` (overview §7).

## 7. State handed to the next story

Record in the report: the measured transcript size per mode, and the doc comment on the sink that
explains the offset constraint (it is where someone about to add compression will read it).
