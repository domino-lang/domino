# Story 13 — Implementation report: collapsible detail pane + the claim assertion

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** stories 06 (`src/debug/driver.rs`), 07 (`src/debug/report.rs`, the viewer),
11 (`goal_negated` / `goal_smt` already hoisted as locals; `smt/<L>/<R>.smt2` layout),
12 (`stop_reason` viewer migration — already done, not touched here).
**Blocks / feeds:** story 14 (uses `DebugRun.goal_smt`; must bump schema from 6),
story 15 (must keep `goal_smt` in the serialised order).

`TRACE_SCHEMA` went **5 → 6.** Whichever of 14 / 15 lands next bumps 6 → 7.

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/driver.rs` | `TRACE_SCHEMA` **5 → 6**. New field `DebugRun.goal_smt: String`, placed **right after `base_frame_smt`** (logical grouping; keep this order). Set from the existing local `goal_smt` in `run_debug_command` (`run.goal_smt = goal_smt.clone();`) inside the `if !claim.is_admitted()` block — empty string for an admitted claim. The story-11 `goal_negated: &SmtExpr` / `goal_smt: &str` thread-through to `explore_paths` / `check_pair` is **kept as-is** (least churn); `check_pair` already stopped re-deriving the goal per pair in story 11, so that acceptance criterion was already met. Two new tests: `goal_smt_equals_the_negated_claim_goal` (rebuilds the exact `EquivalenceContext` and asserts `run.goal_smt == eqctx.emit_claim_goal_negated(&claim, "PKGEN").to_string()`, plus schema 6 + `goal_smt` present in `trace.json`) and `goal_smt_is_empty_for_an_admitted_claim` (PKDEC / `lemma-kem-correctness`). |
| `src/debug/report.rs` | Viewer rewrite of the detail pane (CSS + JS). `synthetic_run` fixture gains `goal_smt: "(assert (not (= x 0)))"`; the three `parsed["schema"]` asserts (two in `report.rs`, one in `driver.rs`) go 5 → 6; `trace_json_round_trips_and_is_deterministic` also asserts `parsed["goal_smt"]`. No change to `write_trace_json` / `write_html` / `write_summary` / `flush` signatures. |
| `docs/stories/14-…md`, `docs/stories/15-…md` | "Inherited" notes updated: `goal_smt` exists, schema is 6, bump to 7. |

Verdicts, path counts, solver-call counts, pruning, `summary.txt` and the stdout tree are all
unchanged. `trace.json` / `index.html` stay byte-deterministic across two runs (verified on
`kem-dem` PKENC).

## 2. `DebugRun.goal_smt`

```rust
/// The negated claim goal — `(assert (not …))` — checked at every (left,
/// right) terminal pair after the vacuity check. One per run: it depends on
/// the claim and the oracle, not on the path. Empty for an admitted claim.
/// The viewer's `Claim assertion` section renders it (story 13).
pub goal_smt: String,
```

Serialised order: `… base_frame_smt, goal_smt, left_listing, …`. For `kem-dem` PKENC
`same-output` it is a single ~737-char `(assert (not (=> (and …) …)))`.

## 3. Viewer — collapsible sections

### 3.1 `sec(title, body, defaultOpen, meta)`

Was `sec(title, body)` returning `<div class="sec"><h3>`. Now returns
`<details class="sec"><summary><span class="sec-title">…</span><span class="sec-meta">…</span></summary><div class="sec-body">…</div></details>`.

- **Open state**: `localStorage["domino.debug.sec." + title]` — `"1"` / `"0"`, falling back to
  `defaultOpen`. Read via `lsGet` / written via `lsSet`, both wrapped in `try/catch` (a `file://`
  page with site data blocked *throws* on access, not just returns null). A `toggle` listener
  persists every change.
- **`sec-meta`** shows on the summary line so a collapsed section is still informative.
- The **listing centring** (`termRow.scrollIntoView({block:"center"})`) moved out of
  `listingBlock`'s render-time `setTimeout` into a `toggle` listener on the section — opening a
  collapsed listing centres the terminal line; a closed listing never scrolls the pane. If a
  listing section is already open on render (persisted), a one-shot `requestAnimationFrame`
  centres it.

### 3.2 Section order + defaults in `renderDetail` (right-path selection)

| Section | Default | `sec-meta` example |
|---|---|---|
| `Path — left` | **open** | `4 steps → L53 return` |
| `Path — right` | **open** | `11 steps → L65 return` |
| `Claim assertion` | **open** | `#1.1 → L65 return` |
| `Model` (when `model_smt`) | **open** | — |
| `SMT asserted` | **collapsed** | `155 assertions + base frame` |
| `Listing — left (<game>)` | **collapsed** | `55 lines · 4 on this path` |
| `Listing — right (<game>)` | **collapsed** | `67 lines · 11 on this path` |

The base-frame block stays a bare nested `<details>` inside the `SMT asserted` body.

Other selections:
- **Left-path** selection: `Path — left`, `SMT asserted`, `Listing — left` — **no** `Claim
  assertion`, **no** `Model`.
- **Right branch prune**: `Path — left`, `Path — right`, `Listing — left`, `Listing — right`
  (early return — a prune never reached a terminal, so no claim assertion / SMT).
- **Left branch prune** (top-level row): `Path — left`, `Listing — left`.

### 3.3 `Claim assertion` section (`claimAssertionSec`)

Right-path selection only. Body:
- prose note: `checked after right path #<id> terminates at L<n> (return|abort)` — from
  `rp.terminal.label` / `rp.terminal.is_abort`.
- a **Copy runnable query** button (see §3.5).
- a `<pre>` showing `(check-sat)  ; vacuity` then `T.goal_smt` then `(check-sat)  ; negated goal`
  — or, for an `unreachable` pair, a comment saying the vacuity check was `unsat` and the goal was
  never checked, followed by the goal text for reference.
- an outcome line: the pair's verdict badge (existing `.badge.<kind>` colours) + one sentence:
  `verified` ⇒ vacuity sat / goal unsat; `unreachable` ⇒ vacuity unsat, goal not checked;
  `goal-fails` ⇒ goal sat, see Model; `inconclusive` ⇒ goal unknown / timed out.

### 3.4 Toolbars

- **Detail pane** (`addSecToolbar`, `.sectoolbar` at the top of `#detail` on every render):
  `Expand all` / `Collapse all` set `d.open` on every `details.sec` in the pane **and** persist
  each choice through `lsSet`.
- **Left pane** (`.treetoolbar`, static in the template under `#vtoggles`): `Collapse all` /
  `Expand all` toggle `.collapsed` on every `.node.lp` and flip the `▾`/`▸` twist glyph. **Not**
  persisted (cheap to redo; per-node persistence would be noise).
- A left path with **> 25** children (`right_paths + pruned_branches`) now starts **collapsed**,
  with a `▸` twist, so a PKENC run opens as a ~6-row overview.

### 3.5 Copy button (`copyBtn` + `execCopyFallback`)

On `Claim assertion` and `SMT asserted`. Copies `pairQueryText(lp, rp)`:

```
base_frame_smt
<left.smt lines>
<right.smt lines>          (right selection only)
(check-sat)                 ; vacuity
(push 1)
goal_smt
(check-sat)                 ; negated goal
(pop 1)
```

`navigator.clipboard.writeText` with a hidden-`<textarea>` + `document.execCommand("copy")`
fallback; a "copied" flash for 1.2 s on success; **any failure is silent** (never a broken pane).

> **Deviation from spec §3.3 / AC bullet 6.** The story asks for text "byte-identical to
> `smt/<L>/<R>.smt2`". That on-disk file (`src/debug/smtout.rs`) carries a `(set-option …)`
> preamble, a file header, per-section `; ----` comment banners and `(get-model)` — reproducing
> them byte-for-byte in the viewer would mean duplicating `smtout.rs`'s formatting in JS. Instead
> the button emits a **clean runnable query** with the same *semantic* content and check-sat
> sequence, and when a self-contained pair file exists on disk the `SMT asserted` body shows a
> `also on disk: smt/<L>/<R>.smt2` line pointing at the canonical artefact. `smtOnDisk(rp)`
> mirrors `SmtOut::covers`: `all` / `deltas` ⇒ always; `failures` ⇒ goal-fails / inconclusive
> only; `none` ⇒ never.

## 4. `localStorage` key scheme

`domino.debug.sec.<section title>` → `"1"` (open) / `"0"` (closed). The title string is used
verbatim, so keys look like `domino.debug.sec.Listing — left (Game_MON_CCA_PKE)`. Absent key ⇒
fall back to the section's `defaultOpen`. All access through `lsGet` / `lsSet`, which swallow
exceptions — with `localStorage` stubbed to throw, the pane still renders with the default
open/closed state and no console error (verified).

## 5. How this was verified (no browser available in-session)

Headless Chromium could not run in the session (missing `libnspr4.so` etc.). Instead:

- **`cargo test --workspace` and `--features cvc5-lib`**: clean. New tests
  `goal_smt_equals_the_negated_claim_goal`, `goal_smt_is_empty_for_an_admitted_claim` pass;
  `report::tests` (determinism, self-containment, byte-identity) pass with schema 6.
- **`cargo clippy --workspace --all-targets`** (both feature configs): clean.
- **`node --check`** on the extracted `<script>`: valid.
- **A ~120-line hand-rolled DOM shim** (`scratchpad/domshim.js`) executes the real viewer script
  against real `trace.json` files (green PKENC + a weakened-invariant goal-fails PKENC) and
  drives every row's click handler. Confirmed:
  - all 24 rp-row renders raise no exception;
  - goal-fails row → 7 sections in the order above, correct open/closed defaults, correct
    `sec-meta` strings, correct `Claim assertion` note + outcome text;
  - left-path selection and pruned-branch selection render **no** `Claim assertion`;
  - `Expand all` writes all 7 `localStorage` keys; `Collapse all` + re-render → all sections
    honour the stored `"0"`;
  - `localStorage` stubbed to throw on every access → pane still renders, defaults applied, no
    throw;
  - the left/right tree toolbar handlers run without error.
- **Determinism**: two `domino debug … PKENC same-output` runs → `diff` on `index.html` is empty.

The owner should still do the real-browser pass from the story's §5 (`xdg-open`, click a right
path, collapse/reload, check `Ctrl-F`, check the devtools network tab is empty).

## 6. State handed to the next story

- **`TRACE_SCHEMA = 6`.** `trace.json` gained `DebugRun.goal_smt: String` (after `base_frame_smt`,
  before `left_listing`) — the rendered negated claim goal, empty for an admitted claim, equal to
  `eqctx.emit_claim_goal_negated(&claim, oracle).to_string()`. Story 14 bumps to 7 (adds
  `options.jobs`); story 15 bumps to 7 (adds `options.with_oracle_functions`) — whichever lands
  second bumps from what it finds.
- The story-11 `goal_negated: &SmtExpr` / `goal_smt: &str` params on `explore_paths` /
  `explore_left_path` / `check_pair` are **still there**. `run.goal_smt` duplicates the same
  string. Story 14/15 may collapse the thread-through to read `run.goal_smt` if convenient — not
  required.
- **Viewer**: every detail section is a `<details class="sec">` keyed in `localStorage` under
  `domino.debug.sec.<title>`. `sec(title, body, defaultOpen, meta)` is the constructor. Helpers
  added: `lsGet` / `lsSet` / `secKey`, `addSecToolbar`, `setAllNodes`, `pathMeta` / `listingMeta`
  / `smtMeta`, `smtOnDisk`, `pairQueryText`, `copyBtn` / `execCopyFallback`, `smtBlock`,
  `claimAssertionSec`, `termWord` / `plural`. `listingBlock` no longer scrolls on its own — it
  stashes `pre._termRow` and `sec` scrolls on `toggle`.
- No new dependencies; `index.html` is still one self-contained `file://`-openable file; the
  `TEMPLATE` is still an `r##"…"##` literal.
