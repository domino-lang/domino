# Story 31 — implementation report

## What changed

- `src/easycrypt/transcript.rs` (new): the record format of `ec-transcript.jsonl`, in one place.
  - `GOALS_PER_STEP` (3) and `GOAL_TEXT_CAP` (12 000) live here now, documented as the contract
    between the transcript and the live page. `tactics::live` imports them; `tactics` re-exports
    them as before.
  - `EcTranscriptMode { Capped (default), Full }`.
  - `record(mode, tag, ctx, sentence, ms, answer) -> String`: the story-27 record, with the answer
    verbatim (`Full`) or capped (`Capped`).
  - `cap_response(answer) -> Option<String>`: every top-level field but `proof` is kept verbatim and
    in order (`version`, `state`, `status`, `error`, `messages`). `proof` becomes
    `{"goals_dropped": m, "goals": [{"id", "text" (cut at 12 000 chars), "text_dropped": k}, ≤3]}`.
    The structured goal (`hyps`, `concl`, …) is left out: it is the bulk of an answer and nothing
    reads it back from the transcript. `goals_dropped`/`text_dropped` are always written, so a capped
    record is recognisable. An answer that is not a JSON object is written verbatim.
  - Parsing uses `RawValue` (new serde_json feature `raw_value` in the root `Cargo.toml`).
    serde_json scans a `RawValue` and skips unknown fields iteratively, so capping a deeply nested
    goal needs no big stack and runs on the caller's thread.
  - **The module doc comment explains the offset constraint** ("do not compact, compress, rotate or
    rewrite; cap harder here instead"), repeated on `session::TranscriptSink`.
- `Session` (`src/easycrypt/session.rs`):
  - `set_transcript_sink(writer, path, mode, tag)`: it now takes the path (for diagnostics) and the
    mode.
  - Writes go through `write_record`. On a failed write: under `Full`,
    `SessionError::Transcript { path, source }` ("could not write the EasyCrypt transcript `<path>`
    (`--ec-transcript full`): <cause>"). Under `Capped`, the sink is dropped, one `warning:` line
    naming the path and the cause goes to stderr, `SessionEvent::TranscriptDropped { path, cause }`
    goes to the observer, and `send` carries on (`record_bytes: None` from then on).
  - `transcript_dropped() -> bool`.
- `run_tactics` (`src/easycrypt/tactics/mod.rs`): `TacticsOptions::ec_transcript`. The transcript
  file is an `Option<File>` shared across equivalences; when a session reports
  `transcript_dropped()`, later equivalences get no sink (a later record would start at an offset
  the page does not know, after a possibly half-written one).
- Live page (`tactics/live/`):
  - `Step { line, offset, len }` became `Step { record: Option<RecordSpan { line, offset, len }> }`.
    The line and offset counters only advance for steps that have a record. A step without one
    is never read from the transcript. Its detail says "no transcript record" and "goal text not
    embedded; the transcript was not written for this step".
  - `read_goal_texts` reads `goals_dropped`/`text_dropped` when present: `total = goals +
    goals_dropped`, `cut = chars - cap + text_dropped`. So a capped record renders exactly like a
    full one.
  - The footer no longer says the transcript holds "EasyCrypt's full answer". It now says the goals
    are cut the same way unless the run had `--ec-transcript full`. The wording is the same in both
    modes, so the page stays identical across them.
- CLI (`crates/domino`): `--ec-transcript <capped|full>` (requires `--tactics`, default `capped`),
  `EcTranscriptArg` mapped to `EcTranscriptMode`.
- Docs: `CONTEXT.md` ("EasyCrypt transcript" mentions capping and append-only). Story 33's
  "Inherited" section has a story-31 bullet.

## Measured (kem-dem `--tactics --proofstep 0 --oracle PKGEN`, debug build)

| mode | `ec-transcript.jsonl` | records | `index.html` |
|---|---|---|---|
| story 28 (verbatim) | 4.06 MB | — | 74.8 kB |
| `capped` (default) | **251 773 B (≈ 0.25 MB)** | 27 | 74 219 B |
| `full` | **4 061 294 B (4.06 MB)** | 27 | 74 218 B |

About 16x smaller. The two pages are identical once `strip_timings` is applied (checked by
script); the one-byte size difference is in the timings element. By the same ratio the whole
kem-dem theorem (549 MB in story 27) should be around 35 MB capped. That run was not made.

## Verification

- `transcript::tests` (4): 10 goals x 50 000 chars → 3 goals of 12 000, `goals_dropped` 7,
  `text_dropped` 38 000, all other fields equal and in order; short goals and `proof: null` are kept
  whole; **`Full` is the story-27 record byte for byte** against the recorded fixture
  `testdata/easycrypt/story31/answer-two-goals.json` (a real `ec.native cli -json` answer after
  `split.`); a capped record of that fixture keeps both goal texts.
- `session::tests` (4 new, with a stand-in `easycrypt` shell script that `cat`s an answer file, so
  no real EasyCrypt is needed): the sink caps a 10-goal answer (AC 1, at the sink); `Full` writes
  the answer verbatim; a writer failing after 2 records under `Capped` → all 5 sends succeed, 2
  records, exactly one `TranscriptDropped` (naming the path and "No space left on device") between
  the 2nd and 3rd `Answered`, then `record_bytes: None`; under `Full` → `SessionError::Transcript`
  naming the path and the cause.
- `tactics::live::tests` (3 new): the page is the same from a capped and a full transcript
  (oversized goals, 5 goals, cut notes); steps after a drop render without goal text and no step
  claims a record past the drop; **end to end**: a `Session` with a failing capped sink and the
  `LiveHandle` as observer: 4 sentences all `ok`, one warning, and the page renders every step.
- `tactics::tests::live::the_page_is_the_same_under_a_capped_and_a_full_transcript` (needs
  `DOMINO_EASYCRYPT`, hello-world, both modes): same `strip_timings(index.html)`, the capped
  transcript is smaller, and only the capped one has `goals_dropped`.
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: no warnings.
- `cargo test --workspace` (with `DOMINO_EASYCRYPT=easycrypt/ec.native`): all pass (sspverif 489
  passed, 5 ignored). With `--features cvc5-lib`: 553 passed, 1 failed, 6 ignored. The one failure
  is the known `debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim`, which predates
  story 23 (see the reports of stories 23, 24, 26, 27). The other workspace crates pass.

## Deviations and notes

- **A capped goal keeps only `id` and `text`**, not a truncated structured goal. The story's
  "~36 kB per record" implies this: the text is all the page reads. Anything that later wants the
  structured goal from the transcript needs `--ec-transcript full`.
- The warning goes to stderr through `eprintln!` from `Session`. It can briefly disturb a
  `--progress bar` line, as any stderr line does. The observer event exists so callers and tests
  can see it.
- The cut notes on the page still say "see transcript record N". Under `capped` that record states
  how much was cut but does not hold the rest. The footer now says this. The per-step note was left
  alone so that the page stays identical across modes.
- The measurement runs deleted `example-projects/kem-dem/kem-dem-cca-ssp/_build/easycrypt` between
  runs (`--force` is story 32). It is git-ignored build output.

## State handed to the next story

- Transcript size per mode: kem-dem PKGEN **0.25 MB capped, 4.06 MB full** (27 records).
- The doc comment explaining the offset constraint is at the top of
  `src/easycrypt/transcript.rs` (and on `TranscriptSink` in `session.rs`). Anyone adding
  compression reads it there.
- A tactics run no longer dies on a full disk under the default mode. Story 33's "a full disk"
  case now concerns the proof files, not the transcript.
- `Session::set_transcript_sink` takes `(writer, path, mode, tag)`; `SessionEvent` has a fourth
  variant, `TranscriptDropped`, and matches on it must handle it.
