# Story 28 — implementation report

## What changed

- `src/easycrypt/tactics/live/` (new, `mod.rs`, `page.rs`, `tests.rs`): the live translation page.
  - `LiveHandle` (`Rc<RefCell<Live>>`) is the one observer of a `--tactics` run. It keeps a model
    (equivalences, oracles, the goal tree, the steps of each goal) and rewrites
    `_build/easycrypt/<theorem>/progress/index.html` (atomic write: temp file and rename).
    Writes are throttled to one per 500 ms; `equivalence_started`, `oracle_finished`,
    `lockstep_done`, `activity`, `finish` and `fail` force one. `finish` (also on error: `fail`) is
    the last write, without the refresh tag.
  - `page.rs`: the HTML, inline CSS and JS, no network, dark mode, one file.
  - `strip_timings(html)` removes the one timings element (see below).
- `Session` (`src/easycrypt/session.rs`): `set_observer(Box<dyn FnMut(&SessionEvent)>)`.
  `SessionEvent::{Sending, Waiting, Answered}`: `Waiting` is sent every `WAIT_TICK` (1 s) while a
  sentence runs (the wait loop slices `recv_timeout`; without an observer nothing changed), and
  `Answered` carries the response and the size of the transcript record just written.
- Prover (`driver.rs`): a `live: Option<LiveHandle>` field. `prove_node` is a wrapper around
  `prove_node_inner` that reports `node_entered`/`node_left` (label `N<idx>`, kind, the `J`/`S` ids
  below the node, the lockstep node); `oracle` reports the router prelude as the root goal;
  `note_rung` names the rung about to be tried (`0: auto => /#`, `ladder: smt()`, `ladder: premise
  unfolded, smt`, and the same `with hints`); `admit` reports the admit with its label.
- `run_tactics_observed(…, progress: Box<dyn ExportObserver>, phases)`; `run_tactics` is a wrapper
  with the null observer. The page is written by both. Every equivalence and oracle is reported to
  the page, and to `--progress`.
- `--progress` (story 21) now covers `tactics`: `ExportPhase::Tactics`, one item per oracle (`Eq_A_B
  PKENC`, a phase per equivalence) and a new `ExportEvent::GoalFinished { oracle, goal, admitted }`
  per joint node. `PhaseLog` / `LoggingExportObserver` remember the export phases (name, item count)
  so the page can list them. `main.rs` builds one observer for the export and a fresh one for each
  theorem's tactics.
- The old unconditional `eprintln!("tactics: oracle …")` of story 27 is gone (the progress line
  `tactics i/n: Eq_A_B <oracle>` replaces it, and `--progress none` silences it).

## The page

```
header   theorem; chips: the export phases that ran (name, items), then `tactics (running|done|failed)`;
         "working on: Eq_A_B.ec > PKENC > N7 synchronized" (or what the run does between goals:
         opening the proof, lockstep execution, easycrypt compile); the pending command,
         "waiting for EasyCrypt (12 s): `smt(...)`" with a spinner; elapsed
summary  oracles done, goals closed, admits by reason (story 27's counts); a table of admits:
         id, reason, link to the goal
per equivalence   file, proofstep, report file; per oracle a <details>: status chip, closed /
         undone / fallbacks, lockstep counts, link to the lockstep page (`../…/easycrypt/index.html`),
         then the goal tree:
           goal = one joint node (`N7 synchronized [J3 J4 +2] tree rung: ladder: smt() closed|open|admitted`)
             - `admit` rows: the exact comment written in the `.ec` (`(* domino: J3 … *)`)
             - steps, in order: badge accepted / failed / undone / timed out, the sentence, the error
               text (200 characters inline, 2000 in the detail), the time
             - child goals, nested
```

The router prelude is the root goal of each oracle (`router prelude`), `N0` its child. Sentences
outside any oracle (the proof's opening, the base case, the `admit.` of goals not asked for) are
counted, not listed.

Interaction (inline JS): clicking a step shows its detail (record number in the transcript,
messages, error, the goal text if embedded). The selected step, the goals opened or closed by hand
and the scroll offset live in `location.hash` (`sel=s12&o=n0_0_3.1&y=340`), which survives the
refresh. Summary links jump to a goal and open its ancestors. Goals on the path to the current one
and goals with admits are open by default.

### Statuses

`accepted` / `failed` (EasyCrypt `error`) / `timed out` (`interrupted`) come from the response.
`undone` is derived: an `undo N.` marks every accepted sentence of the session whose depth is
above `N` (the session is a stack of depths; `undo` sentences themselves are not listed). A goal is
`open` while the prover is in it, `closed` when left, `admitted` when it holds an `admit`.

## Embedding rule for goal text

A step keeps its sentence, status, error text and messages (cut at 2000 characters), all small. The
goal text is **not** kept in memory: the model remembers the byte offset and length of the step's
record in `ec-transcript.jsonl` (`Session` reports the record size; the page counts). At write time
the goals of the *shown* steps are read back from there, once per step (cached), on a thread with a
1 GiB stack (goals nest deeply, as in story 27):

- the pending step: the goals it is applied to (the previous answer);
- the newest 12 steps of the goal being worked on;
- the last step of every goal.

Each shown step embeds at most `GOALS_PER_STEP` = 3 goals, each cut at `GOAL_TEXT_CAP` = 12000
characters; a cut says how many characters or goals are missing and at which transcript record to
find them. Every other step says "goal text not embedded ... record N". The final page shows only
the last step of each goal. So the page grows with the number of goals (joint nodes), bounded by
`nodes x 3 x 12 kB` for the goal text plus about 300 bytes per sentence, and not with the number
of sentences or the size of a goal. The transcript is never embedded.

## Timings

All timings (each step's EasyCrypt time, the oracle's EasyCrypt time, the elapsed time, the age of
the pending command) are in `<script id="timings" type="application/json">` and rendered into
`<span data-t="…">` placeholders by the JS, which also ticks the pending and elapsed times between
refreshes. Nothing else on the page varies between runs of an unchanged project:
`strip_timings(page_a) == strip_timings(page_b)` (tested on two hello-world runs).

## Measurements

| run | steps in the page | page | `ec-transcript.jsonl` |
|---|---|---|---|
| kem-dem `--oracle PKGEN` (debug build, 6.2 s) | 14 | 74.8 kB | 4.06 MB |

kem-dem `PKENC` and the whole theorem were **not** run here (the instruction not to run kem-dem
`--tactics`, and the disk had 2 GiB free: story 27 measured 549 MB of transcript for the whole
theorem). The bound for them follows from the rule: `PKENC` has 43 nodes, so at most 43 x 3 x 12 kB
= 1.5 MB of goal text in the final page, plus a few hundred bytes for each of a few thousand
sentences, against a transcript of hundreds of MB. While running, the page adds the 12 newest steps
of the current goal (at most 36 goals x 12 kB more). Rewrite cost: goal text of a step is parsed once
(cache), the rest of the page is rendered from the model; a flush is at most every 500 ms.

## Verification

- Unit tests (`easycrypt::tactics::live`, 14): pending sentence and refresh tag on the page; the
  final page has no refresh tag and no pending command, and lists the export phases; a failed run
  says so; steps land in their goal with status, error text, rung, the admit label and the summary
  row; `undo` marks exactly the later sentences as undone; only the last step of a goal (and, while
  running, the current goal) has goal text; the cut and its pointer, and the size of a page with
  oversized goals; throttling, and the final write anyway; the timings element is the only
  difference between two runs; HTML escaping; the header's activity; relative links.
- `session::tests::the_observer_sees_the_sentence_ticks_while_it_runs_and_the_answer`: a stand-in
  `easycrypt` script (no real EasyCrypt needed) that takes 2.3 s: `Sending`, two `Waiting`,
  `Answered`.
- `progress::tests::logging_observer_remembers_phases_per_theorem_and_the_write_phase`.
- With `DOMINO_EASYCRYPT` (hello-world): `the_live_page_shows_the_oracle_its_goals_and_ends_without_a_refresh_tag`,
  and `two_runs_on_an_unchanged_project_write_the_same_file` now also compares the stripped pages.
- Browser (headless Google Chrome, `--screenshot`, on the kem-dem `PKGEN` run): the final page
  renders (dark mode, phase chips, summary, oracle), `#sel=s22` opens the ancestors, selects the
  step and scrolls to it with its goal text below; the JS ran without errors. Mid-run pages were
  captured every 250 ms during the run (54 pages: with the refresh tag, growing step lists, "working
  on" naming the oracle and node; the last one without the tag).
  **Not verified by eye:** the spinner line of a slow sentence in a real browser. PKGEN's sentences
  all take under 300 ms, so no captured page had one pending past the throttle; it is covered by the
  unit test and the tick test above.

## Deviations and notes

- **The page starts when the tactics start, not during the export.** The export phases (seconds) are
  listed as chips, taken from a `PhaseLog`, and are not live on the page: the theorem's output
  directory does not exist before the `write` phase, and every theorem is exported before any is
  written (story 21). `--progress` on stderr covers the export live.
- **"The steps on the currently expanded goal"**: a static page cannot know which goal the reader
  expanded, so it embeds the goal the *prover* is at (its newest 12 steps) plus the last step of each
  goal. Reading an older step of another goal means the transcript record named in the detail.
- The pending step's goal text is the answer before it (what it is applied to); the sentence has no
  answer yet.
- A sentence that starts within 500 ms of the last write is not on the page until the next tick
  (1 s), so a command that finishes in under about a second is never shown as pending.
- `Live` is single-threaded (`Rc<RefCell>`); the `Session` with an observer is not `Send`.
  Nothing needed it to be.
- Old `eprintln!` line of story 27 removed (see above); the plain progress lines replace it.
- Rung 0 is recorded per goal as `0: auto => /#` when tried; a goal closed by it shows that rung.

## State for the next stories

- Story 29 can read the admit rows and the rung of each goal from the model
  (`Live::eqs[..].oracles[..].nodes[..]`); the page needs no change to show more reasons (the
  summary table is by slug).
- Adding a new kind of event: extend `ExportEvent` (non-exhaustive) and `LiveHandle`; the
  prover-side hooks are `Prover::live` (`prove_node`, `oracle`, `note_rung`, `admit`).
