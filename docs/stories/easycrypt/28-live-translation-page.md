# Story 28 — Live translation page and EasyCrypt transcript

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 21 (export phases), 24 (tree widget, refresh convention), 27 (`--tactics`,
transcript).
**Blocks:** nothing.

---

## 1. Why this story exists

A `--tactics` run spends most of its time in EasyCrypt: `smt` calls, trial tactics, undo. The
owner wants to watch it: *"a live progress report when the translation is going on … visually as
an html file while domino is applying heuristics and waiting for EasyCrypt. Also, being able to
see easycrypt output on the form."*

On overhead: an EasyCrypt command costs from 0.1 s to several seconds, while rewriting a page
costs milliseconds and is throttled. The large part is goal text: 4WHS `inv` record literals run
to hundreds of lines. So the page embeds goal text **only for the steps it shows**. The full JSON
stays in the transcript.

## 2. Inherited from earlier stories

- **Story 27:**
  - `_build/easycrypt/<theorem>/progress/ec-transcript.jsonl` (every sentence, including undone
    attempts, with its full response);
  - the per-oracle walk: joint node → tactic → subgoals, with rung 0, ladder rungs and fallbacks;
  - the report reasons.
- **Story 24:**
  - the joint-tree widget;
  - `<meta http-equiv="refresh" content="2">` while running, removed at the end, flushes throttled
    to at most 2 per second;
  - selections kept in `location.hash`;
  - self-contained HTML in a Rust raw string.
- **Story 21:** export phase names and the `ExportEvent` observer.

## 3. Work to do

1. `domino easycrypt --tactics` writes `_build/easycrypt/<theorem>/progress/index.html`, and
   rewrites it after every EasyCrypt response (throttled).
2. **Header.** The current phase (the export phases from story 21, then `tactics`), the current
   equivalence, oracle and joint node, and the time elapsed. A spinner shows "waiting for
   EasyCrypt (12 s): `smt(get_setE mem_set).`" while a command is pending.
3. **Body.** Per equivalence and oracle, the goal tree under construction:
   - each EasyCrypt goal with its joint node (`J`/`S` ids, linking to the lockstep page of story
     23/24);
   - the tactics tried, in order, each marked accepted / failed (error text) / undone / timed out;
   - the ladder rung reached;
   - the goal's status: open, closed, or admitted with its reason.
4. **EasyCrypt output.** Clicking a step shows EasyCrypt's response to it: the `pp` of every goal
   it left (hypotheses and conclusion), its messages and its error. Only the `pp` text of shown
   steps is embedded, generated on demand by the writer from the transcript: the pending step, the
   steps on the currently expanded goal, and the last step of each goal. Everything else is in
   `ec-transcript.jsonl`, and the page says so.
5. The final write drops the refresh tag and adds the report summary (story 27's counts per
   reason) at the top.
6. `--progress` on stderr keeps working as in story 21, extended with a `tactics` phase that
   reports per oracle and per goal.

## 4. Acceptance criteria

- [ ] During a kem-dem `--tactics` run, the page refreshes, shows the pending EasyCrypt command,
      and keeps the selection across refreshes. Verify this in a browser.
- [ ] Every admit in the written `Eq_*.ec` can be found on the page with its reason, and the
      failed attempts before it show their EasyCrypt error text.
- [ ] Page size stays bounded on a large run: record the size at the end of a kem-dem run and
      explain how it scales.
- [ ] Two runs on an unchanged project produce the same final page, except for timings. Keep
      timings in one clearly separated element so a test can strip them.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh; export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --tactics --proofstep 0 &
open _build/easycrypt/*/progress/index.html
```

## 6. Notes / risks

- Throttle, but always write the final state. The last thing the page shows must match the file on
  disk.
- Don't add a web server. `file://` with meta refresh is the agreed mechanism.

## 7. State handed to the next story

Record in the report: the page layout, the embedding rule for goal text, and the measured page and
transcript sizes.
