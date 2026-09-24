# Story 24 — Joint-tree viewer, per-relation sub-verdicts, live refresh

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 23 (lockstep engine, trace schema 9).
**Blocks:** 28 (the live translation page reuses its tree widget and refresh mechanism).

---

## 1. Why this story exists

Story 23 writes the lockstep joint tree to `trace.json` and `summary.txt`, but no HTML. The
existing viewer (`src/debug/report.rs`, symbolic-execution stories 07/13/16) draws a **left-path →
right-paths** tree, which is the wrong shape for lockstep.

The owner wants the HTML report to be where they connect an EasyCrypt `admit` to what Domino knows
("note down where we get stuck in the html report so user can connect it to EasyCrypt admits"). The
owner also wants `domino debug --easycrypt` to show its progress live in the page, not only on
stderr.

## 2. Inherited from earlier stories

- `src/debug/report.rs` (≈1700 lines):
  - `pub fn flush(run, out_dir)` writes `trace.json` + `index.html`;
  - the HTML is a Rust raw string, `const TEMPLATE: &str = r##"…"##`; keep the `r##` delimiters;
  - it is self-contained, with no network access.
- Viewer features that must carry over:
  - the collapsible detail pane with the claim assertion (story 13);
  - executed-line painting of both listings per path (story 16; painting is driven by labels, and
    since story 22 plumbing guards are labelled too);
  - pruned-branch cut lines (story 08).
- Trace schema 9 (story 23 §3.4): joint nodes with kinds, per-side labels and consumed labels,
  `plumbing` flag, stuck points with reasons, terminal pairs with equal-output/invariant verdicts
  and per-relation sub-verdicts.

## 3. Work to do

1. **Joint tree.** One collapsible tree. Each node shows its kind, both sides' labels and
   decisions, e.g. `L42 if → then | R57 if → then  [synchronized]`. Split nodes list their
   surviving combinations and mark pruned ones. **Plumbing** nodes are dimmed, and a toggle hides
   them.
2. **Leaves.** A terminal pair shows two verdict chips, **equal-output** and **invariant**. When
   the invariant isn't verified, a nested list shows each relation's sub-verdict. Links go to the
   model / SMT file, as today.
3. **Stuck points.** Each gets a badge (`S3`) on its node and an entry in a "Stuck points" panel.
   The entry shows the labels, the reason and a rollup of the Domino verdicts of every terminal
   pair **below** it: "S3: 4 pairs below; equal-output verified 4/4; invariant verified 3/4,
   `Domino_rel_keys` fails on J7". This rollup is how the owner answers "is this admit verified in
   Domino or inconclusive there too".
4. **Listings.** Selecting a joint path paints both listings as story 16 does, using the consumed
   labels of every node on the path.
5. **Live refresh.** While the run is in progress, every `flush` writes the page with
   `<meta http-equiv="refresh" content="2">`. The final write omits it. Throttle flushes to at
   most two per second. This must work from `file://` with no server: a browser blocks `fetch` of
   local files, so polling a JSON sidecar is not an option. Selections are lost on refresh; keep
   them in `location.hash` so they survive, and don't store them anywhere else.
6. Remove story 23's placeholder page.

## 4. Acceptance criteria

- [ ] kem-dem `PKENC`, `PKDEC` and hello-world `UsefulOracle` render. Every joint path can be
      selected, and painting, cut lines and collapsible panes work against the EasyCrypt listing.
      Verify this in a browser, not only by reading the HTML.
- [ ] Each stuck point's rollup matches a count computed independently from `trace.json` (test).
- [ ] While a run is active, the page refreshes itself and keeps the selection. After the run, the
      page has no refresh tag.
- [ ] Two runs on an unchanged project produce byte-identical `index.html`.
- [ ] Sequential (non-`--easycrypt`) `index.html` is byte-identical to before the story.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D debug --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC &
open _build/debug/*/*/PKDEC/easycrypt/index.html     # watch it fill, then settle
```

## 6. Notes / risks

- Keep the page self-contained: all CSS and JS inline, as the existing template does.
- Large joint trees: render lazily (expand on click), as the sequential viewer's collapsible panes
  do.

## 7. State handed to the next story

Record in the report:

- the tree widget's structure and how it is fed from the trace;
- the refresh and `location.hash` convention.

Story 28 builds the translation page from the same pieces.
