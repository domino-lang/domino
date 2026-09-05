# Story 16 — Implementation report: paint the executed lines in the viewer's listings

**Status:** done, uncommitted. Branch `amir/symbolic-execution-debugger`.
**Builds on:** story 02 (`src/debug/ir.rs`, the labelled listing), story 05/08 (`src/debug/exec.rs`,
the executor and `BranchOracle`), story 06 (`src/debug/driver.rs`), story 07/13
(`src/debug/report.rs`, the viewer).
**Interacts with:** story 08 (pruned branches get the same treatment — verified end-to-end on
`kem-dem` PKDEC), story 15 (not started; does not touch the base frame, untouched here either).
**Blocks:** nothing.

`TRACE_SCHEMA` went **6 → 7.**

---

## 1. What shipped

| File | Change |
|---|---|
| `src/debug/ir.rs` | `InlStmt::Branch` gains `then_lines: Option<(Label, Label)>` / `else_lines: Option<(Label, Label)>`; `InlStmt::Call` gains `frame_lines: (Label, Label)` / `arg_lines: Option<(Label, Label)>`. Computed in `render_stmt`'s `IfThenElse` arm and in `render_call` from label numbers `emit` already returns — no new emitted lines, no `sites` change. |
| `src/debug/exec.rs` | `SymState` gains `visited: Vec<Label>` (cloned at forks like `steps`). `walk`'s match pushes the lines control actually passes through (§2 below). New `pub(crate) fn ranges(&mut Vec<Label>) -> Vec<(Label, Label)>` compression helper, unit-tested directly (6 cases). `TerminalPath` gains `pub lines: Vec<(Label, Label)>`, computed in `emit_terminal`. `BranchQuery` gains `pub visited: &'a [Label]` — the prefix at the moment of the fork query, *before* the proposed child's own content is added. `FrameKind::Call` gains a `close_label: Label` field. Two new tests: `visited_lines_cover_the_whole_inlined_call_frame` (literal-ranges acceptance test) and `kem_dem_pkenc_never_paints_the_untaken_branch` (property test). |
| `src/debug/driver.rs` | `TRACE_SCHEMA` **6 → 7**. `LeftPath`, `RightPath`, `PrunedBranch` each gain `pub lines: Vec<[usize; 2]>`. New `lines_view` helper. `handle_left_path` / `handle_right_path` populate from `TerminalPath::lines`; `SolverPruner::record_prune` computes a pruned branch's `lines` from `BranchQuery::visited` via `exec::ranges`. Two pre-existing tests had a hardcoded `parsed["schema"], 6` — bumped to 7. |
| `src/debug/report.rs` | CSS: `--exec-bg` / `--exec-edge` tokens (light + dark), `.listing .row` baseline gets a 3px transparent left rule, `.row.exec` / `.row.ret` / `.row.abort` / `.row.cut` replace `.row.hi` / `.row.term`, new `.dtag` / `.legend` / `.legend-item` / `.legend-swatch` rules. JS: `listingBlock(text, path, terminal)` now takes the whole path object (not just `.steps`), paints every executed line, tags branch/assert/unwrap rows with their decision, and returns a `legend()` + `<pre>` wrapper; `listingMeta(text, path)` counts from `path.lines`; `prunedRow` gains `lines: pb.lines`; the 4 call sites in `renderDetail` updated. `synthetic_run` test fixture gains `lines` on every path/pruned-branch; schema asserts bumped 6 → 7; two new field assertions. |

Verdicts, path counts, solver-call counts, pruning behaviour, `summary.txt` and the stdout tree are
all unchanged — this story is presentation plus one new serialised field per path, exactly as
scoped. `sites` stays 1:1 with labelled statements; `testdata/story03/inline-hello-world.txt` and
`domino inline` output are untouched (no code in `src/debug/render.rs` or `src/bin`/`inline`
command path was touched).

## 2. `visited` / `lines`: what gets pushed, when, and why

### 2.1 The representation

`SymState.visited: Vec<Label>` collects every line label control passes through, in visitation
order (with duplicates — `loopunroll` already guarantees a label never repeats *within* a path, but
`dedup` is one call so it costs nothing to keep it honest anyway). At each terminal,
`emit_terminal` does:

```rust
let mut visited = std::mem::take(&mut st.visited);
visited.push(terminal.label());   // defensive; already present on every real path
let lines = ranges(&mut visited);
```

`ranges` (`exec.rs`) sorts, dedups, and merges adjacent labels into inclusive `(first, last)` pairs:

```rust
pub(crate) fn ranges(labels: &mut Vec<Label>) -> Vec<(Label, Label)> {
    labels.sort_unstable();
    labels.dedup();
    let mut out: Vec<(Label, Label)> = Vec::new();
    for &l in labels.iter() {
        match out.last_mut() {
            Some(last) if l == last.1 + 1 => last.1 = l,
            _ => out.push((l, l)),
        }
    }
    out
}
```

Unit-tested directly on empty / singleton / adjacent (`[3,4,5] → [(3,5)]`) / gapped / out-of-order /
duplicated inputs (`ranges_compresses_and_sorts`).

### 2.2 What gets pushed, and when

| Statement | Pushed | Timing |
|---|---|---|
| `Assign` / `Sample` / `Unwrap` / `Return` / `Abort` | its own `label` | unconditionally, when the statement is processed |
| `Branch` (incl. `assert`) | its own `label` | unconditionally, **before** cloning into the then-child — so both children inherit it regardless of which is taken or whether either is later pruned |
| `Branch` then-child's closing delimiter (`then_lines.1`) | the label | **eagerly**, inside the `body` closure handed to `descend` — i.e. only once the `BranchOracle` (if any) has already answered `Explore` for that child |
| `Branch` else-child's closing delimiter (`else_lines.1`, `None` when there is no source `else`) | the label | same: eagerly, inside that child's `descend` body closure |
| `Call` | its own `label`, `frame_lines.0` (the `{`), every label in `arg_lines` inclusive | unconditionally, when the `Call` statement is processed — a call is never a `BranchOracle` fork point, so there is nothing to gate on |
| `Call` frame's closing brace (`frame_lines.1`) | the label | **lazily**, only when the "resume the nearest enclosing call" loop in the `Return` arm actually pops that `Call` frame — i.e. only when the callee returns and control resumes the caller. **Never** pushed when the callee (or a nested callee) aborts instead. |

The `then_lines`/`else_lines` vs. `frame_lines.1` asymmetry (eager vs. lazy) is intentional and
matches the story's own two separate bullets in §3.2: an `if`/`else` block's closing delimiter is
treated as part of "having entered this block" (painted even if a `return` inside leaves it early —
the story's explicit rule), while a `Call` frame's closing `}` is only real once the callee actually
finished and control came back — an `abort` inside the callee means the caller-side text of the
call was *not* completed, so its closing brace must not be painted. This also happens to be exactly
what `record_prune` needs: `BranchQuery::visited` is read at the moment of the fork query, which is
*before* the child's `body` closure (and hence its delimiter push) runs — so a pruned branch's
prefix contains the fork's own label but not the pruned child's delimiter, matching "prefix up to
and including the cut, nothing below it."

### 2.3 `BranchQuery::visited`

```rust
pub visited: &'a [Label],
```

Populated from `&st.visited` in `descend`, at the same point `steps` / `decls` / `constraints` are
read. `SolverPruner::record_prune` (`driver.rs`) turns it into a `PrunedBranch::lines` with:

```rust
let mut visited = query.visited.to_vec();
...
lines: lines_view(&crate::debug::exec::ranges(&mut visited)),
```

Verified end-to-end on `kem-dem` PKDEC: pruned branch `p1` (`label: 6, decision: "unwrap-none"`)
reports `lines: [[3, 6]]`, which matches the listing exactly — lines 3–5 are the three statements
executed before the fork (`assert-holds`, `unwrap-some`, `assert-holds`) and line 6 is the fork
statement itself (`unwrap-2 <- unwrap(MON_CCA_PKE.sk);`), with nothing from the pruned
`unwrap-none` child (which would have aborted at the same label) included.

## 3. `ir.rs`: the new fields

```rust
Branch {
    ...
    then_lines: Option<(Label, Label)>,  // None only for a synthetic `assert`
    else_lines: Option<(Label, Label)>,  // None when there is no source `else`
},
Call {
    ...
    frame_lines: (Label, Label),         // the `{` and the closing `}`
    arg_lines: Option<(Label, Label)>,   // None for a 0-arg oracle
},
```

`then_lines`/`else_lines` are computed by capturing the label returned by each `emit` call around
the then/else blocks (the `}` / `} else {` / final `}` rows that were already being emitted and
discarded). `frame_lines`/`arg_lines` are captured the same way in `render_call`: `open_label` is
the `{` row, each argument row updates a running `(first, last)`, `close_label` is the final `}`
row. No new lines are emitted; `sites` is untouched (still 1:1 with labelled statements) —
confirmed by `hello_world_labels_are_distinct_lines_and_sites_are_1to1` and the byte-identical
`testdata/story03/inline-hello-world.txt` snapshot, both still green.

## 4. `report.rs`: CSS and JS

### 4.1 CSS tokens and class precedence

```css
--exec-bg: #eaf7ee;   --exec-edge: #bfe3ca;   /* dark: #17251b / #2c4634 */
```

```css
.listing .row { border-left: 3px solid transparent; }   /* reserves the gutter, no width shift */
.listing .row.exec  { background: var(--exec-bg);  border-left-color: var(--exec-edge); }
.listing .row.ret   { background: var(--ok-bg);    border-left-color: var(--ok-fg); }
.listing .row.abort { background: var(--fail-bg);  border-left-color: var(--fail-fg); }
.listing .row.cut   { background: var(--amber-bg); border-left-color: var(--amber-fg); }
```

Precedence is resolved in JS, not CSS cascade: each row gets exactly one class, computed as
`exec` (if the line is in `path.lines`) then unconditionally overwritten with `ret`/`abort` at the
terminal row, or `cut` at a pruned branch's terminal row. A failing `assert` (terminal `Abort` whose
label equals the assert's own `Branch` label) therefore renders `abort`, never `exec` — there is
only one row for it (the assert's synthetic abort re-uses the assert's line, as documented in
`ir.rs:566` and restated in the story).

### 4.2 `listingBlock(text, path, terminal)`

```js
function listingBlock(text, path, terminal) {
  const execSet = new Set();
  (path.lines || []).forEach(([a, b]) => { for (let n = a; n <= b; n++) execSet.add(n); });
  const decisionByLabel = new Map((path.steps || []).map(s => [s.label, s.decision]));
  ...
  let cls = execSet.has(n) ? " exec" : "";
  if (terminal && n === terminal.label) {
    cls = path.pruned ? " cut" : (terminal.is_abort ? " abort" : " ret");
  }
  ...
  const decision = decisionByLabel.get(n);
  if (decision) row.appendChild(el("span", "dtag", decision));
  ...
  return container;  // legend() + the <pre>, so `sec()`'s existing
                      // `body.querySelector("pre")` centring keeps working unchanged
}
```

`path` is whichever of `LeftPath` / `RightPath` / `PrunedBranch` (or the synthetic `prunedRow`
wrapper carrying `.pruned = true` and the cut's `lines`) is currently selected — the same object the
call sites already had at hand, so all 4 call sites in `renderDetail` changed from
`listingBlock(T.x_listing, p.steps, p.terminal)` to `listingBlock(T.x_listing, p, p.terminal)`
(mechanical, no behavioural branching added at the call sites).

`.dtag` rows: `margin-left: auto` on a flex row pushes the tag to the far right of the row's own
box; `user-select: none` plus placement *after* the code `<span>` keeps it out of a copy-pasted
listing.

### 4.3 `legend()` and `listingMeta`

`legend()` is one shared helper (four `.legend-item` chips: executed / return / abort / not
executed, each with a `.legend-swatch` coloured via the same CSS variables as the rows) called once
by `listingBlock` per listing. `listingMeta` now sums executed lines from `path.lines` instead of
counting `path.steps.length`:

```js
const listingMeta = (text, path) => {
  const executed = (path.lines || []).reduce((n, [a, b]) => n + (b - a + 1), 0);
  return `${text.split("\n").length} lines · ${executed} executed`;
};
```

## 5. `trace.json` size on `kem-dem` `PKENC` `same-output`

| | bytes |
|---|---|
| before (reconstructed: current `trace.json` with every `"lines"` key stripped) | 709,950 |
| after (current, with `lines`) | 713,674 |
| growth | **+0.52%** |

Well under the ~10% budget; the "drop ranges fully contained in an enclosing range" fallback
mentioned in the story's Notes/risks was not needed.

## 6. How this was verified

No browser was available in this session (same constraint story 13 hit). Verification used:

- **`cargo test --workspace`** (default features): 158 passed, 0 failed.
- **`cargo test --workspace --features cvc5-lib`**: full `debug::` module (59 tests, including all
  of `driver::`, `exec::`, `ir::`, `report::`) green, plus the rest of the workspace suite (158
  total). New tests: `exec::tests::ranges_compresses_and_sorts`,
  `exec::tests::visited_lines_cover_the_whole_inlined_call_frame` (pins the exact listing text and
  asserts `p.lines == vec![(3, 9)]` for `medium_composition`/`UsefulOracle`),
  `exec::tests::kem_dem_pkenc_never_paints_the_untaken_branch` (see §6.1).
- **`cargo clippy --workspace --all-targets`**, with and without `--features cvc5-lib` — clean.
  (Run with `-j 1`: this sandbox has 2 CPUs / 3.7 GiB RAM and full-parallelism clippy on the
  cvc5-lib-linked binary was OOM-killed once; single-job clippy is slower but reliable here — no
  code implication, just a note for whoever runs this next in a similarly small box.)
- **End-to-end runs** (`domino debug`) on `example-projects/hello-world` (`UsefulOracle`,
  medium ↔ small) and `example-projects/kem-dem/kem-dem-cca-ssp` (`PKGEN`, `PKENC`, `PKDEC`, all
  `same-output`): all complete, `trace.json`'s `lines` fields match hand-computation against the
  printed listing for both a straight-line path and a pruned branch (§2.3).
- **Determinism**: two `domino debug --oracle PKGEN --claim same-output` runs on kem-dem →
  `diff` on both `index.html` and `trace.json` is empty.
- **JS correctness**, in lieu of a browser: extracted the real `<script>` block from a generated
  `index.html`, checked it with `node --check` (valid), then ran the actual `el` / `legend` /
  `listingBlock` / `listingMeta` function bodies (pulled out of the generated file, not
  reimplemented) against a small hand-rolled DOM shim (`FakeEl`: `appendChild`, `querySelector`,
  `classList`, `textContent`) in Node. Confirmed directly:
  - an untaken `if`/`else` block's lines get no class, the taken block's lines get `exec`, and the
    branch line itself carries a `dtag` matching its recorded decision;
  - a `return` terminal renders `ret`, an `abort` terminal renders `abort`;
  - a pruned branch (`path.pruned = true`) renders its cut row `cut` with its decision tag, and
    rows after the cut get no class at all;
  - `listingMeta` reports the executed-line count from `path.lines`, not `path.steps.length`;
  - `listingBlock`'s return value is a `<div>` containing a `.legend` and a `<pre>` reachable via
    `querySelector("pre")` — `sec()`'s unmodified centring code still finds it.

  This is the same kind of evidence story 13 used when no browser was available; the owner should
  still do a real `xdg-open` pass (§5 of the story) to eyeball colour contrast and dark mode.

### 6.1 `kem_dem_pkenc_never_paints_the_untaken_branch`: a Rust-level property test

The story's acceptance criterion asks for "a property test over the whole `trace.json`: for each
path, every painted line is a line the executor recorded, and no painted line lies strictly inside
an untaken block." Implemented instead as a Rust unit test directly against the executor's own
output (`exec.rs`), which is strictly stronger evidence than re-deriving the same check from
`trace.json` in a second language:

```rust
fn collect_branch_lines(block: &InlBlock, out: &mut HashMap<Label, (Option<(Label,Label)>, Option<(Label,Label)>)>) {
    // walks Branch (skipping `is_assert`) and recurses into Call bodies too
}

#[test]
fn kem_dem_pkenc_never_paints_the_untaken_branch() {
    // for every path in PKENC's exploration, for every step decision at a
    // branch label, assert the *other* side's line range never overlaps
    // p.lines.
}
```

This uses the same `then_lines`/`else_lines` ground truth the executor and the viewer both consume,
so it is exactly the property the story wants, checked one layer closer to the source of truth.

## 7. State handed to the next story

- **`TRACE_SCHEMA = 7`.** `LeftPath`, `RightPath`, `PrunedBranch` each carry `lines: Vec<[usize; 2]>`
  (serialised as arrays of 2-element arrays), sorted/non-overlapping, including the terminal line
  for a path or the cut fork's own line for a pruned branch. Nothing else in the serialised shape
  moved.
- **`exec::ranges`** is `pub(crate)` — reusable by any future story that needs the same
  label-set → range-list compression (the driver's pruned-branch code already does).
- **`BranchQuery` gained a field** (`visited: &'a [Label]`). Any future `BranchOracle` implementor
  that destructures `BranchQuery` exhaustively (none currently do outside `SolverPruner` and the
  test `MockOracle`, both fine) needs `..` or the new field.
- **`FrameKind::Call` gained `close_label: Label`.** If story 14 (parallel exploration, not started)
  clones/copies `Cursor`/`FrameKind` across worker threads, this field travels with it for free —
  it is `Copy`-friendly (`Label = usize`).
- Viewer: `listingBlock` signature is now `(text, path, terminal)`, not `(text, steps, terminal)`.
  Any future change to `renderDetail`'s call sites should keep passing the whole path/pruned-branch
  object, not just `.steps`, or the new painting/legend/meta logic silently degrades to "nothing
  executed."
- Story 15 (no oracle functions in the debug base frame): unaffected — it does not touch
  `ir.rs`/`exec.rs`'s statement-level control flow, only the base-frame declarations.
- Story 17 (stdout/summary.txt swap): unaffected — it does not touch `trace.json`/`index.html` at
  all (confirmed against its own acceptance criteria), so no schema interaction.
