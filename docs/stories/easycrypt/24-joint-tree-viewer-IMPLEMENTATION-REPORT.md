# Story 24 — implementation report

## What changed

- `src/debug/lockstep_viewer.rs` (new): `render_html(trace_json, rollups, live)`, `stuck_rollups`,
  `without_refresh`. The page template is `src/debug/lockstep_viewer.html` (`include_str!`); all CSS
  and JS are inline, no network.
- `src/debug/report.rs`: the stylesheet and the story-18 effect renderer moved out of the sequential
  template into `VIEWER_CSS` / `EFFECT_JS`, spliced back at `__VIEWER_CSS__` / `__EFFECT_JS__`, and
  shared by the joint-tree page. Sequential `index.html` is byte-identical (kem-dem `PKENC`
  `--claim same-output`, diffed against the pre-change binary).
- `src/debug/lockstep_report.rs`: `flush(meta, outcome, summary, out_dir, live)` writes the viewer;
  the placeholder is gone.
- `src/debug/lockstep_run.rs`: partial flushes are time-throttled (`FlushThrottle`, 500 ms gap, so at
  most two a second) from `node_entered` and `pair_checked`, replacing "every 8 joint paths". The
  final write is `live = false`. A run that ends in an error rewrites the page on disk without the
  refresh tag (`settle_page`).

## State handed to the next story

### The tree widget and how it is fed

`index.html` embeds two JSON blocks: `#trace` (the schema-9 `trace.json`, compact) and `#rollups`
(`stuck_rollups`, not part of `trace.json`, so the schema is unchanged). The JS indexes
`tree.nodes` (arena, node 0 root) with a `parentOf` map built from the `explored` children.

- One `.node` per joint node: `[#index] <edge> ▸ <heads> [kind] [S badge] [J id, two verdict chips]`.
  The edge is what the parent's decision point did, e.g. `L42 if → then | R57 if → then`; heads are
  where each side stands at the node, e.g. `L43 if | R58 if`. Pruned and unexplored children are
  rows without a node (struck through, `✂ pruned (query: answer)`).
- Children are built the first time a node opens. A trace of at most 250 nodes opens fully; a bigger
  one opens only along single-child runs. `Expand all` builds everything.
- Plumbing nodes (`left.plumbing` or `right.plumbing`) are dimmed; the checkbox hides their rows
  (their subtrees stay).
- Detail pane for any node, or a pruned child: verdicts (with model links and `smt/<J>.smt2` when the
  `--smt` mode wrote it), the root-to-node path table with source lines, solver answers, effect
  columns and negated goals for a joint path, and both listings painted. The executed set is the
  union of `consumed` of every node on the path plus the edge decision labels; for a joint path the
  `PairRecord` lines are added too, because `consumed` leaves out the closing-brace lines.
- Stuck panel: one entry per `S<n>` with the reason, labels and the rollup text
  (`1 pair below; equal-output verified 1/1; invariant verified 0/1 (1 GOAL FAILS), Domino_x fails on J7`).

### Refresh and `location.hash`

- A page written during the run has `<meta http-equiv="refresh" content="2">` as the first tag after
  `<meta charset>`; the final page has none. The page shows a RUNNING chip iff the tag is present.
- The selection lives only in `location.hash`, written with `history.replaceState`:
  `n=<node>[&c=<child index of a pruned/unexplored child>]`, `plumb=hide`, `ts=`/`ds=` (tree and
  detail scroll offsets). Node indices are stable while a run is in progress. Not kept across a
  refresh: which tree nodes the reader opened or collapsed, and the open state of detail sections.
- Story 28 can reuse `nodeEl` / `ensureKids` / `select` / `writeHash` / `restore`, and `render_html`'s
  `live` flag and the throttle.

## Deviations and notes

- The template is a separate `.html` file included with `include_str!`, not a Rust raw string.
- The page does not use `localStorage` (the sequential viewer does for section state): the story
  says selections live in the hash only.
- A process killed by SIGKILL leaves a page that refreshes forever; Ctrl-C and errors are settled.
- The 4WHS and yao projects were not run (hard rule).

## Verification

Tests (viewer unit tests run in the default build; the run-level ones need `cvc5-lib`): rollups
against an independent count from `trace.json` (`each_stuck_points_rollup_matches_a_count_taken_from_trace_json`),
refresh tag live/final, byte-identical `index.html` across two runs, embedded trace equals
`trace.json`, throttle. Browser (headless Chrome, screenshots and `--dump-dom`) on kem-dem `PKENC`,
`PKDEC`, hello-world `UsefulOracle` and the rule oracles `StuckOrder` and `SplitPruned`: selection
by hash, painting, cut lines, plumbing toggle, stuck panel, and that a live page keeps its selection
after the reload.

## Notes for follow-up

- `driver::tests::goal_smt_is_empty_for_an_admitted_claim` fails under `--features cvc5-lib` (predates this story, see story 23's report).
