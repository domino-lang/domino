# Story 13 — Collapsible detail pane and the claim assertion in `index.html`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 07 (`src/debug/report.rs`, the viewer), story 06 (`src/debug/driver.rs`).
**Interacts with:** story 11 (the same goal assertion is written into `smt/<L>/<R>.smt2`).
**Blocks:** nothing.

---

## 1. Why this story exists

The viewer's right-hand detail pane renders **every** section fully expanded, always, in this
order: `Path — left`, `Path — right`, `Listing — left`, `Listing — right`, `SMT asserted`,
`Model` (`report.rs:465` `renderDetail`). For `kem-dem` `PKENC` the two listings are hundreds of
lines each, so selecting a pair means scrolling past two full program listings to reach the SMT,
and the base frame — the one genuinely huge block — is the only thing behind a `<details>`
(`:512`).

And the pane never shows **the actual claim assertion the solver was asked about**. `check_pair`
(`driver.rs:920`) does the vacuity `check-sat`, then pushes
`eqctx.emit_claim_goal_negated(claim, oracle)` (`:935`) and checks again — that negated goal is
the whole question, and it appears nowhere in `trace.json` or the HTML.

### What the owner asked for

> In the html output, it's very nice but I want the right pane which includes the paths, listings,
> and assertions to be collapsible (I want listings and SMTs to be collapsible). Also I want the
> claim assertion that is sent to the solver after the right path also hits termination (return,
> abort).

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Mechanism** | Native `<details>`/`<summary>` per section — no framework, no dependency, keyboard-accessible, and `Ctrl-F` still finds text in an open section. |
| **Persistence** | Open/closed state per section title in `localStorage`, so it survives selecting another path and re-opening the file. |
| **Defaults** | `Path — left/right` **open**; `Listing — …` **collapsed**; `SMT asserted` **collapsed**; `Claim assertion` **open**; `Model` **open**. |
| **Claim assertion** | Rendered from a new `DebugRun.goal_smt` — one string per run (the negated goal depends only on the claim and the oracle, not on the path). |
| **Verdicts** | Unchanged. Presentation + one new serialised field. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The viewer — `src/debug/report.rs` (story 07)

- `write_html` (`:48`) splices `serde_json::to_string(run)` into `TEMPLATE` (`:65`) at
  `__TRACE_JSON__`, escaping `<` as `<`. The file is **self-contained**: all CSS and JS
  inline, no fetches, opens from `file://` offline. Keep it that way.
- Layout: `header` (title, subtitle, option chips, summary chips) + `#left` (filter box, verdict
  checkboxes, `#tree`) + `#detail`.
- `#tree` rows: one `.node.lp` per left path with a `.lp-head` and a `.rp-list` of `.rp` rows;
  the `▾` twist toggles `.collapsed` on the node (`:370`, `:388`). Clicking a row calls
  `select(domNode, lp, rp)` (`:416`) → `renderDetail(lp, rp)` (`:465`).
- Detail helpers: `sec(title, body)` (`:445`) builds `<div class="sec"><h3>title</h3>…`;
  `listingBlock(text, steps, terminal)` (`:426`) renders the whole listing with `.hi` on path
  lines and `.term` on the terminal line, and `scrollIntoView`s the terminal;
  `stepsTable(steps, sites)` (`:452`).
- CSS: `.sec` (`:197`), `.sec > h3` (`:198`), `details`/`summary` (`:231`).
- Determinism: two runs of an unchanged project produce byte-identical `trace.json` **and**
  `index.html`. Nothing you add may depend on wall-clock or iteration order of a `HashMap`.

### 2.2 The data the viewer has

`DebugRun` (`driver.rs:165`): `base_frame_smt`, `left_listing`, `right_listing`,
`left_sites` / `right_sites` (`BTreeMap<Label, SiteView>`), `left_paths: Vec<LeftPath>`,
`left_pruned_branches`, `summary`, `left_syntactic: u64`, and `stop_reason: StopReason`
(story 12 — `partial: bool` is **gone**; `run.partial()` is now an accessor).
`LeftPath` (`:288`): `id`, `steps`, `terminal`, `reachable`, `smt: Vec<String>`, `right_paths`,
`pruned_branches`. `RightPath` (`:306`): `id`, `steps`, `terminal`, `verdict`, `model_smt`,
`smt: Vec<String>`. `TRACE_SCHEMA` at `:162` — **now 5** after story 12; bump to 6.

> **Story 12 already migrated the viewer's `partial` chip.** The template reads
> `T.stop_reason` (falling back to `T.partial` for old traces) and renders
> `PARTIAL — exploration stopped early (interrupted by Ctrl-C)` / `(--max-paths N reached)`.
> The "two places" the old spec mentioned are one place on this branch; it is done — do not
> redo it.

### 2.3 The goal assertion

`EquivalenceContext::emit_claim_goal_negated(&self, claim, oracle) -> SmtExpr`
(`src/writers/smt/contexts/equivalence/emit.rs:466`) is a pure function of the claim and the
oracle — **not** of the path. `check_pair` calls it once per pair today.

## 3. Work to do

### 3.1 Driver — hoist the goal onto the run

- In `run_debug_command`, right after `base_frame` is built, compute
  `let goal = eqctx.emit_claim_goal_negated(&claim, oracle);` and store
  `run.goal_smt = goal.to_string()` in a new `DebugRun` field:

  ```rust
  /// The negated claim goal — `(assert (not …))` — checked at every (left,
  /// right) terminal pair after the vacuity check. One per run: it depends on
  /// the claim and the oracle, not on the path. Empty for an admitted claim.
  pub goal_smt: String,
  ```
- Pass the prebuilt `SmtExpr` into `check_pair` instead of re-emitting it per pair (a small win,
  and it makes the "the HTML shows what the solver saw" claim literally true).
- Bump `TRACE_SCHEMA`. If story 11 landed first, reuse whatever it already hoisted rather than
  computing the goal twice.

### 3.2 Viewer — collapsible sections

Replace `sec(title, body)` with:

```js
// key: stable per section title, so the choice persists across selections and reloads.
function sec(title, body, defaultOpen) { … }   // returns a <details class="sec">
```

- `<details class="sec"><summary><span class="sec-title">…</span><span class="sec-meta">…</span></summary>…</details>`.
- Open state: `localStorage["domino.debug.sec." + title]` — `"1"`/`"0"`; falls back to
  `defaultOpen`. Wrap **every** `localStorage` access in `try/catch` (a `file://` page in a
  browser with site data blocked throws on access).
- `summary` shows a useful `sec-meta` when closed so a collapsed section is still informative:
  `Listing — left (Game_MON_CCA_PKE)` → `312 lines · 4 on this path`; `SMT asserted` →
  `<n> assertions`; `Path — right` → `5 steps → L36 return`.
- Add **Expand all** / **Collapse all** buttons in a small toolbar at the top of `#detail`
  (they set every `<details>` in the pane and persist the choice).
- `listingBlock`'s `scrollIntoView` currently fires from a `setTimeout` on render; make it fire on
  the `toggle` event when the section opens instead, so opening a collapsed listing still centres
  the terminal line and a closed listing does not scroll the pane.

Section order and defaults in `renderDetail`:

| Section | Default |
|---|---|
| `Path — left` | open |
| `Path — right` (right selection only) | open |
| `Claim assertion` (right selection only) | open |
| `Model` (when `model_smt`) | open |
| `SMT asserted` | collapsed |
| `Listing — left (<game>)` | collapsed |
| `Listing — right (<game>)` | collapsed |

Note the reorder: the question (`Claim assertion`) and the answer (`Model`) come **before** the
bulk. Keep the existing `base frame` `<details>` nested inside `SMT asserted`.

### 3.3 Viewer — the `Claim assertion` section

For a right-path selection (not for a pruned branch, which never reached a terminal), render:

```text
Claim assertion — checked after right path #3.7 reaches L36 return

  1  (check-sat)                     ; vacuity: is this (left, right) pair reachable at all?
                                     ; answered: sat   → the pair is reachable, goal checked below
  2  (assert (not <goal>))           ; the claim goal, negated
     (check-sat)                     ; answered: sat   → GOAL FAILS   (model below)
```

- The goal text is `T.goal_smt`, in a `<pre>` like the other SMT blocks.
- Above it, one line of prose naming the terminal it was checked at:
  `after right path #3.7 terminates at L36 (return)` / `… at L31 (abort)` — take it from
  `rp.terminal.label` / `rp.terminal.is_abort`.
- Below it, the recorded outcome derived from `rp.verdict`, using the existing badge colours:
  `unreachable` ⇒ say the vacuity check was `unsat` and the goal was **not** checked;
  `verified` ⇒ goal `unsat`; `goal-fails` ⇒ `sat` + a link-ish pointer to the `Model` section;
  `inconclusive` ⇒ `unknown`.
- Add a **Copy** button on this section and on `SMT asserted` that copies
  `base_frame_smt + left.smt + right.smt + goal_smt + "(check-sat)"` to the clipboard — the same
  text story 11 writes to `smt/<L>/<R>.smt2`. Use `navigator.clipboard.writeText` with a
  `document.execCommand("copy")` fallback and a "copied" flash; a failure must be silent, never a
  broken pane. If story 11 landed, mention the on-disk path in the section meta instead of
  duplicating the explanation.

### 3.4 Left pane — unchanged behaviour, one addition

The tree already collapses per left path via the `▾` twist. Add **Collapse all** / **Expand all**
controls next to the verdict checkboxes (`#vtoggles`) that toggle `.collapsed` on every
`.node.lp`, and default a left path's `.rp-list` to **collapsed** when it has more than 25
children, so a `PKENC` run opens as a readable 6-row overview instead of a 100-row wall. Persist
nothing here — it is cheap to re-toggle and per-node persistence would be noise.

## 4. Acceptance criteria

- [ ] `DebugRun.goal_smt` is in `trace.json`, non-empty for a non-admitted run, and equals the
      text the driver asserted (unit test compares it against
      `eqctx.emit_claim_goal_negated(...).to_string()`).
- [ ] `check_pair` no longer re-derives the goal per pair; verdicts for `PKENC` / `same-output`
      are unchanged (compare `trace.json` verdict-by-verdict against a pre-story-13 run).
- [ ] Every detail-pane section is a `<details>`; listings and `SMT asserted` start collapsed,
      paths / claim assertion / model start open; the state survives selecting another path and a
      page reload.
- [ ] With `localStorage` unavailable (test in a private window or by stubbing it to throw), the
      pane still renders with the default open/closed state and no console error.
- [ ] Selecting a right path shows `Claim assertion` with the negated goal, the terminal it was
      checked at, and the recorded outcome matching that pair's badge. Selecting a **left** path
      or a **pruned branch** shows no `Claim assertion` section.
- [ ] The Copy button on a `goal-fails` pair yields text that is byte-identical to that pair's
      `smt/<L>/<R>.smt2` (when story 11 has landed) — or, if not, to
      `base_frame_smt + left.smt + right.smt + goal_smt + (check-sat)`.
- [ ] A collapsed section's summary line still says how big it is (`312 lines · 4 on this path`).
- [ ] Expand all / Collapse all work in both panes.
- [ ] `index.html` is still one self-contained file: no network requests when opened offline
      (check the browser devtools network tab is empty), and it still opens directly from
      `file://`.
- [ ] `index.html` for an unchanged project is byte-identical across two runs.
- [ ] `TRACE_SCHEMA` bumped; `cargo build`/`test`/`clippy --workspace` and `--features cvc5-lib`
      clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
cd example-projects/kem-dem/kem-dem-cca-ssp
D=../../../target/debug/domino
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output

$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
xdg-open $O/index.html      # click a right path; check the section defaults, collapse, reload

# a failing run, to see the Claim assertion + Model pairing
sed -i.bak '/left.pk = right.pk/d' theorem/invariant.smt2
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
xdg-open $O/index.html
mv theorem/invariant.smt2.bak theorem/invariant.smt2

# determinism
$D debug … --oracle PKGEN --claim same-output && cp $O/../../PKGEN/same-output/index.html /tmp/a.html
$D debug … --oracle PKGEN --claim same-output && diff /tmp/a.html $O/../../PKGEN/same-output/index.html
```

Smaller smoke tests first: `example-projects/hello-world`, `example-projects/simple-KEM-example`.

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release`.

## 6. Notes / risks

- **The template is a Rust string literal** (`const TEMPLATE: &str = r##"…"##`). Keep the `r##`
  delimiters; a `"#` sequence inside the JS would end it. Do not reach for a templating crate.
- **`localStorage` throws, not just returns null**, in some `file://` contexts. Every access goes
  through a `try/catch` helper — one unguarded access blanks the whole pane.
- **`<details>` + `Ctrl-F`**: browsers do not search inside a closed `<details>`. That is why the
  filter box in the left pane stays the primary search; do not make the listings the only way to
  find a line.
- **Do not widen scope.** No syntax highlighting, no diff view between left and right listings
  (`domino inline` is story 03's job), no live reload, no new dependencies.

## 7. State handed to the next story

Record in `docs/stories/13-…-IMPLEMENTATION-REPORT.md`: the new `DebugRun.goal_smt` field and
`TRACE_SCHEMA`, the section order and default-open table as implemented, the `localStorage` key
scheme, and screenshots of a right-path selection in both the collapsed and expanded state.
