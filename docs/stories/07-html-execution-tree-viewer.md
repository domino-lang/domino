# Story 07 — HTML execution-tree viewer + `trace.json`

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 06 (`domino debug` and its run structure).
**Blocks:** nothing. This is the last story of the epic.

---

## 1. Why this story exists

From `docs/symbolic-execution-plan.md`:

> I want full log of path conditions and complete incremental transcript passed to solver. I also
> want it to be properly organized, so I can see all the execution paths on the left and execution
> paths on the right induced by the path on the left. It could be visualized in a tree through
> html to be explored?

Story 06 already prints a text tree and writes the transcript. That is enough for a small oracle
and unusable for a real one: a `kem-dem` oracle can have dozens of left paths, each with several
right paths, each carrying tens of path conditions and a page of SMT. Scrollback is the wrong
medium.

So: serialise the run to `trace.json`, and render a **single self-contained `index.html`** over
it. The HTML is *a renderer*, not the source of truth — a future TUI, a CI check, or a diff tool
consumes the same `trace.json`.

## 2. Inherited from story 06

- `domino debug --proof --proofstep --oracle --claim [--check-left] [--no-check-right]
  [--timeout] [--max-paths] [--out]`.
- Artifacts under `_build/debug/<theorem>/<left>-<right>/<oracle>/<claim>/`:
  `transcript.smt2`, `inlined.txt`, `models/<path-id>.smt2`.
- A plain, serialisable run structure (`DebugRun` or whatever story 06 named it) holding:
  theorem/proofstep/oracle/claim identity; both listings with their `sites` maps; ordered left
  paths with their `Step`s; nested right paths with `Step`s and `Verdict`s; model file paths;
  per-node the SMT that was asserted; summary counts.
- `Verdict::{Verified, Unreachable, GoalFails { model }, Inconclusive { model }}`.
- Path ids `#3` and `#3.1`; decisions rendered as `then` / `else` / `assert-holds` /
  `assert-fails` / `unwrap-some` / `unwrap-none`.
- From story 02, `Label` is a **1-based line number** into `InlinedOracle::listing.text`, and
  `listing.sites: BTreeMap<Label, SiteInfo>` with
  `SiteInfo { kind, line, span, pkg_inst_name, oracle_name, depth }`.
- **Left and right line numbers are independent** — they index different listings.

## 3. Work to do

### 3.1 `trace.json`

Add `serde` derives (the crate already depends on `serde` / `serde_derive`; add `serde_json` to
`Cargo.toml` if it is not there) and write the run to `trace.json` in the output directory.

Suggested shape — keep it flat and obvious, it is a debugging artifact, not an API:

```jsonc
{
  "schema": 1,
  "theorem": "kem_dem_cca_ssp",
  "proofstep": 0,
  "left_game_inst": "Game_MON_CCA_PKE",
  "right_game_inst": "Game_MOD_CCA_PKE_Real_KEM",
  "oracle": "PKDEC",
  "claim": "same-output",
  "options": { "check_left": false, "check_right": true, "timeout_ms": null, "max_paths": 1000 },
  "listings": {
    "left":  { "text": "...", "sites": { "12": { "kind": "Branch", "line": "if (k != bot) {",
                                                  "pkg_inst": "MON_CCA_PKE", "oracle": "PKDEC",
                                                  "depth": 1 } } },
    "right": { "text": "...", "sites": { ... } }
  },
  "base_frame_smt": "...",            // the base declarations, for reference
  "left_paths": [
    {
      "id": "#3",
      "steps": [ { "label": 12, "decision": "then" },
                 { "label": 19, "decision": "assert-holds" } ],
      "terminal": { "kind": "return", "label": 27, "text": "return (Some z)" },
      "smt": "...",                   // decls + constraints + return_constraint for this path
      "pruned_branches": [ { "label": 22, "decision": "else" } ],
      "right_paths": [
        {
          "id": "#3.1",
          "steps": [ { "label": 14, "decision": "then" } ],
          "terminal": { "kind": "abort", "label": 31, "text": "abort;" },
          "smt": "...",
          "pruned_branches": [],
          "verdict": "goal-fails",
          "model_file": "models/3.1.smt2",
          "model": "..."              // inline, so index.html stays self-contained
        }
      ]
    }
  ],
  "summary": { "left_paths": 7, "right_paths": 11,
               "verified": 9, "unreachable": 1, "goal_fails": 1, "inconclusive": 0,
               "truncated": false }
}
```

Determinism matters: for an unchanged project, two runs must produce byte-identical
`trace.json` (modulo nothing — no timestamps, no absolute paths, no hash-map iteration order).

### 3.2 `index.html`

One file. **No network access, no CDN, no external assets.** Inline the CSS, the JS and the
`trace.json` payload (as a `<script type="application/json">` block). It must open correctly from
`file://` with the machine offline.

Layout:

- **Header** — theorem, proofstep, `Left == Right`, oracle, claim, the options used, and the
  summary counts as colour-coded chips.
- **Left pane: the tree.** Collapsible. Left paths at the top level, right paths nested beneath
  their left path. Each node shows its id, its step chain (`L12 then → L19 assert-holds → L27 return`),
  and its verdict badge.
  - `verified` — muted green
  - `unreachable` — grey (this is the one people misread; label it *unreachable*, never *ok*)
  - `goal-fails` — red
  - `inconclusive` — amber
  - Pruned branches shown inline, struck through, labelled *pruned (unsat)*.
- **Right pane: detail for the selected node.** Tabs or sections for:
  - **Path** — the step chain with each step's rendered source line pulled from `listing.sites`.
  - **Listing** — the inlined listing with this path's lines highlighted, scrolled to the
    terminal. Left listing when a left node is selected; both when a right node is selected.
  - **SMT** — the exact SMT asserted for this node, in a `<pre>` with horizontal scroll.
  - **Model** — for `goal-fails` / `inconclusive`, the model inline.
- **Filter** — a text box and verdict toggles, so "show me only the failing paths" is one click.

Constraints:

- Wide content (SMT blocks, listing lines) scrolls inside its own container; the page body must
  never scroll horizontally.
- Respect the reader's colour scheme: define the palette on `:root`, override under
  `@media (prefers-color-scheme: dark)`, and give `body` an explicit background.
- No build step. Plain HTML/CSS/JS, generated by a Rust function — a `format!`-based writer or a
  tiny hand-rolled template is fine; do not add a templating dependency.

### 3.3 Where it goes

`src/debug/report.rs`:

```rust
pub fn write_trace_json(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf>;
pub fn write_html(run: &DebugRun, out_dir: &Path) -> std::io::Result<PathBuf>;
```

Called from story 06's driver at the end of the run. `domino debug` prints the path to
`index.html` as its last line.

## 4. Acceptance criteria

- [ ] `domino debug …` writes `trace.json` and `index.html` next to `transcript.smt2`.
- [ ] `index.html` opens from `file://` with no network and renders the full tree.
- [ ] Every tree node's step labels resolve to a line in the corresponding listing, and selecting
      a node highlights exactly those lines.
- [ ] `unreachable` is visually and textually distinct from `verified`.
- [ ] Pruned branches are visible, marked as pruned by an `unsat` check.
- [ ] Filtering to `goal-fails` shows only failing paths.
- [ ] Two consecutive runs on an unchanged project produce byte-identical `trace.json` and
      `index.html`.
- [ ] A `trace.json` from a run with zero failures renders a valid (all-green) page.
- [ ] `cargo build --workspace --features cvc5-lib` and `cargo test --workspace --features cvc5-lib`
      pass. A unit test round-trips a synthetic `DebugRun` through `trace.json`.

## 5. How to verify

```bash
cargo build --workspace --features cvc5-lib

cd example-projects/kem-dem/kem-dem-cca-ssp
cargo run --features cvc5-lib --bin domino -- debug \
    --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC --claim same-output

ls _build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKDEC/same-output/
# -> index.html  trace.json  transcript.smt2  inlined.txt  models/

# open index.html in a browser, offline

# determinism
cp trace.json /tmp/a.json && cargo run --features cvc5-lib --bin domino -- debug ... && diff /tmp/a.json trace.json
```

Then weaken `theorem/invariant.smt2`, rerun, and confirm the failing pair is obvious in the tree
and its model is readable. Restore the file afterwards.

Smaller projects for iterating on the rendering: `example-projects/hello-world`,
`test-projects/test-splitinvoke`.

> **Never** run `debug` against `example-projects/4WHS` or `example-projects/yao` — the two slow
> projects in `example-projects/known-good-slow.txt`. See `docs/stories/00-overview.md` §7.
> If you want a *large* trace to test the viewer's scalability, generate a synthetic `DebugRun`
> in a test rather than proving a big project.

## 6. Notes / risks

- **Size.** A `kem-dem` run's SMT blocks add up. If `index.html` gets unwieldy, keep the per-node
  SMT in `trace.json` and lazily inject it into the DOM rather than pre-rendering every block —
  but keep everything in the one file.
- Do not let the HTML become the source of truth. Anything the page needs must be in
  `trace.json` first.
- Resist adding a JS framework. The page is a tree, a listing and some `<pre>` blocks.

## 7. State handed to the next story

This is the last story of the epic. Record here:

- The final `trace.json` schema (bump `"schema"` if you deviated from §3.1).
- Anything about the viewer a follow-up (a TUI, a CI gate, a diff between two runs) would need.
- Any part of `docs/symbolic-execution-plan.md` that ended up **not** implemented, so it is
  visible rather than quietly dropped.
