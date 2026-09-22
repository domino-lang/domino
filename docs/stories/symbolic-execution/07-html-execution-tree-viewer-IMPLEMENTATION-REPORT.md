# Story 07 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. **Not committed** (commit message at
the bottom). This is the **last story of the epic**.

Read together with `docs/stories/07-html-execution-tree-viewer.md`.

`cargo build --workspace`, `cargo test --workspace` (118 lib tests, +3), `cargo clippy --workspace`
all clean. With the env from `scripts/setup-cvc5-lib.sh` sourced:
`cargo build/test/clippy --workspace --features cvc5-lib` → **124 lib tests** (+3), clean.
`domino prove` / `latex` / `proofsteps` output unchanged.

Hand-verified end-to-end on `example-projects/kem-dem/kem-dem-cca-ssp` proofstep 0 (PKGEN,
PKENC) and `example-projects/hello-world`, including the weakened-`invariant.smt2` failure case
(2 GOAL FAILS → both visible in the tree with inline models; file restored afterwards).

---

## 1. What landed

| File | Change |
|---|---|
| `src/debug/report.rs` | **new** (~430 lines incl. the HTML template + 3 tests). `write_trace_json`, `write_html`, `render_html` + the static single-file viewer template. |
| `src/debug/mod.rs` | `pub mod report;` |
| `src/debug/driver.rs` | `#[derive(Serialize)]` on `DebugRun` + all view types; new `TRACE_SCHEMA`, `OptionsView`, `SiteView`, `sites_view()`. `DebugRun` gained `schema`, `options`, `base_frame_smt`, `left_sites`, `right_sites`; `RightPath` gained `model_smt: Option<String>`. `out_dir` is `#[serde(skip)]`. `check_pair` now returns `(Verdict, Option<String>)` and `write_model` returns `(rel_path, text)`. `run_debug_command` populates the new fields and calls `report::write_trace_json` + `report::write_html` at the end. |
| `crates/domino/src/main.rs` | prints `viewer: <out_dir>/index.html` as the last line (unless the claim is admitted). |
| `Cargo.toml` / `Cargo.lock` | `serde_json = "1.0"` (resolves to the already-locked 1.0.133; one-line lock change). |

No change to `prove`/`latex`/`proofsteps` code paths.

## 2. `trace.json` — the actual schema (`"schema": 1`)

I **deviated from the suggested shape in the story** and kept it flat, matching `DebugRun`
1:1 (the story explicitly allows this — "keep it flat and obvious, it is a debugging artifact,
not an API"). The renderer reads exactly these keys, so a follow-up should treat this as the
contract:

```jsonc
{
  "schema": 1,
  "theorem": "kem_dem_cca_ssp",
  "proofstep": 0,
  "left_game": "Game_MON_CCA_PKE",      // NB: "left_game", not "left_game_inst"
  "right_game": "Game_MOD_CCA_PKE_Real_KEM",
  "oracle": "PKENC",
  "claim": "same-output",
  "admitted": false,
  // "out_dir" is intentionally ABSENT (absolute path -> would break determinism)
  "options": { "check_left": false, "check_right": true, "timeout_ms": null, "max_paths": 1000 },
  "base_frame_smt": "…",                 // everything asserted at solver level 0, rendered
  "left_listing":  "OracleO {\n …",       // \n-separated; line n == Label n
  "right_listing": "…",
  "left_sites":  { "12": { "kind": "branch", "line": "if (k != bot) {",
                           "pkg_inst": "MON_CCA_PKE", "oracle": "PKENC", "depth": 1 }, … },
  "right_sites": { … },
  "left_paths": [
    {
      "id": "1",                          // bare; the UI renders "#1"
      "steps": [ { "label": 12, "line": "if (k != bot) {", "decision": "then" }, … ],
      "terminal": { "label": 27, "line": "return (Some z)", "is_abort": false },
      "reachable": true,                  // false iff --check-left pruned it
      "smt": [ "(declare-const …)", "(assert …)", … ],   // decls ++ constraints ++ return_constraint
      "right_paths": [
        {
          "id": "1.1",
          "steps": [ … ],
          "terminal": { "label": 31, "line": "abort;", "is_abort": true },
          "verdict": { "kind": "goal-fails", "model": "models/1.1.smt2" },
          "model_smt": "(define-fun …)",   // inline, so index.html is self-contained; null otherwise
          "smt": [ … ]
        }
      ]
    }
  ],
  "summary": { "left_paths": 6, "left_pruned": 0, "right_paths": 96,
               "verified": 0, "unreachable": 94, "goal_fails": 2, "inconclusive": 0 },
  "partial": false
}
```

`verdict` is an **internally-tagged** enum: `{"kind":"verified"}`, `{"kind":"unreachable"}`,
`{"kind":"goal-fails","model":"models/1.1.smt2"}`,
`{"kind":"inconclusive","model":null|"models/1.1.smt2"}`. `kind` values are kebab-case.

`step.line` / `terminal.line` are the rendered source line for that label, denormalised onto
each step so the viewer needs no `*_sites` lookup to draw a path chain; `left_sites`/`right_sites`
carry the same `line` plus `kind`/`pkg_inst`/`oracle`/`depth` for every labelled line (not just
the ones on some path).

### Determinism

`serde_json::to_string_pretty` preserves struct field order; `*_sites` are `BTreeMap` (sorted
numerically-as-strings — `"10"` sorts before `"9"`, acceptable for a debug artifact); `out_dir`
is skipped; there are no timestamps. Two runs on an unchanged project produce **byte-identical**
`trace.json` and `index.html` — verified by hand and by
`report::tests::{trace_json_round_trips_and_is_deterministic, html_is_byte_identical_across_runs}`.
(This assumes cvc5's model text is stable across identical queries, which held on every run.)

## 3. `index.html` — the viewer

One self-contained file: inline CSS, inline vanilla JS (no framework, ~250 lines), and the
`trace.json` payload embedded verbatim in `<script type="application/json" id="trace">`. Every
`<` in the JSON is rewritten to `<` before embedding (valid, semantically identical, makes
a `</script>` breakout impossible). **No network access, no CDN, no external assets** — opens
from `file://` offline. `report::tests::html_is_self_contained_and_embeds_the_trace` asserts
there is no `http://` / `https://` and that the embedded JSON still parses.

Layout: header (theorem / proofstep / `L == R` / oracle / claim, options chips, summary chips) →
left pane (filter box + 5 verdict toggles + collapsible tree: left paths, right paths nested) →
right pane (detail for the selected node: **Path** left/right as a step table, **Listing**
left/right with this path's lines highlighted and the terminal line scrolled into view, **SMT**
= collapsible base frame + this path's asserted lines, **Model** inline for goal-fails /
inconclusive).

- Colour scheme: palette on `:root`, overridden under `@media (prefers-color-scheme: dark)`,
  `body` has an explicit background.
- `verified` muted green · `unreachable` grey, labelled *unreachable* (never *ok*) · `goal-fails`
  red · `inconclusive` amber · pruned left paths struck through, badge *pruned (unsat)*.
- Wide content (`<pre>`, listing rows) scrolls inside its own `overflow-x:auto` box; the page
  body never scrolls horizontally.
- Filter: substring match on path id + source text + decision; verdict toggles hide
  non-matching right paths and collapse left paths with no visible child.

**Size.** The whole run (base frame + every path's SMT + models) is embedded once as JSON and
the per-node SMT/model `<pre>` is built lazily on selection (not pre-rendered). Observed:
hello-world 112 KB, kem-dem PKGEN 756 KB, kem-dem PKENC (96 right paths, 2 models) 3.7 MB — all
well under the 16 MB budget. `base_frame_smt` dominates and is stored exactly once.

## 4. Acceptance criteria — status

All met.

- [x] `domino debug …` writes `trace.json` and `index.html` next to `transcript.smt2`.
- [x] `index.html` opens from `file://` with no network; renders the full tree (headless
      DOM-shim smoke test over the 3 traces exercises tree build, node selection, listing
      highlight, filter, verdict toggles).
- [x] Every step label resolves to a listing line; selecting a node highlights exactly those
      lines and scrolls to the terminal.
- [x] `unreachable` is visually (grey) and textually (*unreachable*) distinct from `verified`.
- [x] Pruned branches visible — **per left path only** (see §6); struck-through, *pruned (unsat)*.
- [x] Filtering to `goal-fails` shows only failing paths.
- [x] Two consecutive runs → byte-identical `trace.json` and `index.html`.
- [x] Zero-failure run renders an all-green page (hello-world, kem-dem PKGEN).
- [x] `cargo build/test --workspace --features cvc5-lib` pass; a unit test round-trips a
      synthetic `DebugRun` through `trace.json`.

## 5. Tests

`src/debug/report.rs` `mod tests` (**default build**, no `cvc5-lib` needed):

| test | checks |
|---|---|
| `trace_json_round_trips_and_is_deterministic` | synthetic `DebugRun` → `trace.json`; independent of `out_dir`; re-parses; `verdict.kind == "goal-fails"`, `summary`, `left_sites` all present |
| `html_is_self_contained_and_embeds_the_trace` | starts `<!doctype html>`; no `http(s)://`; embedded JSON parses after `<`-escaping |
| `html_is_byte_identical_across_runs` | two `write_html` calls with different `out_dir` → identical bytes |

The story-06 driver tests are unchanged and still green (the `Verdict` enum shape is unchanged;
only `check_pair`'s return type changed, internal to the module).

## 6. Notes for follow-up

- **`trace.json` schema is flat, not the story's nested draft.** Keys are `left_game` /
  `right_game` (not `*_game_inst`), listings + sites are top-level (`left_listing`,
  `left_sites`, …) not under a `listings` object, and there is no `pruned_branches` array.
  Bump `TRACE_SCHEMA` (`src/debug/driver.rs`) + `report.rs`'s doc if you change any of this.
- **No per-branch pruning info**, because story 05's `execute_streaming` streams terminals
  only (no branch-point callback — see story 06 report §8). The only pruning the run can
  express is *whole left path* (`LeftPath.reachable == false` under `--check-left`), and that
  is what the viewer shows. If story 05 ever grows a branch hook, add a `pruned_branches` field
  to `LeftPath`/`RightPath` and render it inline in the tree (the CSS class `.badge.pruned` is
  already there).
- **`cargo clippy --workspace --features cvc5-lib --all-targets`** flags 4
  `field_reassign_with_default` warnings in `src/debug/driver.rs`'s **story-06 test module**
  (`opts.timeout_ms = Some(1)` etc.). Pre-existing, not touched by this story, not in the
  non-test lint set. Left alone to keep this commit's diff to story 07.
- **cvc5 model determinism** is assumed for the byte-identical-`trace.json` criterion. It held
  on every run here; if a future cvc5 bump makes models non-deterministic, the fix is to stop
  embedding `model_smt` / `base_frame_smt` verbatim, or to canonicalise them.
- Dev machine disk runs ~95–100 % full; `rm -rf target/debug/incremental` reclaims ~1.7 GB.

## 7. What of `docs/symbolic-execution-plan.md` is NOT implemented

The plan is fully covered by stories 01–07 with these known gaps, all already recorded in
earlier story reports:

- **Branch-level solver guidance / pruning** (plan: "asking the solver at every branching
  point"). Story 06 asks the solver **per terminal pair** (vacuity), not per branch, because
  story 05 ships terminal-only streaming. Sound but chatty; the `unreachable` counts are high
  as a result. See story 05 report §"Consistency check" and story 06 report §8.
- **`GameIdentifier::Const` / table-index consts used directly in an oracle expression** —
  not seeded into the symbolic store (nothing in the corpus hits it). Story 06 report §3.
- **`domino inline`** (story 03) was in the epic plan but is **still unbuilt** — `src/debug/
  render.rs::side_by_side` is the minimal shared renderer it was meant to build on.

## 8. Commit message

```
Story 07: HTML execution-tree viewer + trace.json

Serialises a `domino debug` run to `trace.json` and renders a
self-contained `index.html` tree viewer over it, written next to
`transcript.smt2` at the end of every non-admitted run. `domino debug`
prints the viewer path as its last line.

`src/debug/report.rs` (new): `write_trace_json` + `write_html`. The HTML
is one file — inline CSS, inline vanilla JS, and the trace embedded as a
`<script type="application/json">` block with `<` escaped. No network, no
CDN; opens from `file://` offline. Left pane: collapsible tree of left
paths with their induced right paths, verdict badges (verified / grey
*unreachable* / red goal-fails / amber inconclusive), pruned left paths
struck through. Right pane: the selected node's step chain, the inlined
listing with its lines highlighted, the exact SMT asserted, and the model
inline for failures. Filter box + verdict toggles.

`DebugRun` and its view types get `#[derive(Serialize)]` (serde_derive,
already a dep; +serde_json). New fields: `schema`, `options`,
`base_frame_smt`, `left_sites`/`right_sites`, and `RightPath.model_smt`
(inline model text). `out_dir` is `#[serde(skip)]` and there are no
timestamps, so two runs on an unchanged project produce byte-identical
`trace.json` and `index.html`. The JSON schema is flat (1:1 with
`DebugRun`), not the nested draft in the story — documented in the report.

cargo test --workspace and --workspace --features cvc5-lib both pass
(+3 tests: synthetic DebugRun round-trip, HTML self-containment, HTML
determinism); clippy clean; `domino prove` output unchanged.

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01BrBZJz8hq9fqSkecgKfM6H
```
