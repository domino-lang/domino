# Story 16 — Paint the executed lines in the viewer's listings

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 02 (`src/debug/ir.rs`, the labelled listing), story 05 (`src/debug/exec.rs`),
story 06 (`src/debug/driver.rs`), story 07/13 (`src/debug/report.rs`, the viewer).
**Interacts with:** story 08 (pruned branches get the same treatment), story 15 (does not touch the
base frame).
**Blocks:** nothing.

---

## 1. Why this story exists

`listingBlock` (`report.rs:734`) paints exactly the lines that appear in `steps` — i.e. only the
**branching decisions** — amber, plus the terminal line in red:

```js
const hi = new Set(steps.map(s => s.label));
… "row" + (hi.has(n) ? " hi" : "") + (terminal && n === terminal.label ? " term" : "")
```

So in a 300-line `PKENC` listing four scattered amber rows are lit and everything in between —
the assignments, samples, asserts, the inlined call frames that actually ran — is the same
colour as the code that never ran. Worse, an amber `if (b) {` row does not say **which way it
went**: the reader has to jump back to the `Path — left` table (or the path chain in the tree) to
learn that `L14` was `else`, then map that back onto the two blocks under it by eye.

### What the owner asked for

> I want that the html view that shows inlined oracles highlight all lines of code that are
> executed in that path. Now decision points are colored but I have to look up to the PATH in the
> beginning to know which branch is taken. I think the rule could be that executed lines would be
> light green leading to return points. However, mark abort points with red. If a branch is not
> taken do not color it.

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Where the truth comes from** | The **executor records** the lines it walked. Nothing is reconstructed in JS from indentation or brace matching — the viewer paints a set it is handed. |
| **Encoding** | Inclusive line **ranges** (`Vec<[usize; 2]>`, sorted, non-overlapping) per path, not a list of line numbers: a path through a 300-line listing is a handful of ranges instead of 200 integers, and `trace.json` stays small. |
| **Colours** | executed → light green (`--exec-bg`); the terminal `return` line → stronger green (`--ok-bg` + a `--ok-fg` left rule); an `abort` terminal → red (`--fail-bg` + a `--fail-fg` left rule). Untaken branches: **no colour at all**. |
| **Amber** | Retired from the listing. It survives in one place only: the **cut line** of a pruned branch (story 08), which is genuinely "explored up to here, then unsat". |
| **Branch outcome inline** | Every executed branch / assert / unwrap row also shows its decision as a small tag at the end of the row (`then`, `else`, `assert-holds`, `unwrap-none`), so the taken side is readable without the steps table. |
| **Structural lines** | `{`, `} else {`, `}` and a call frame's argument-binding lines are painted **iff their block was entered**. They carry no label today; story 16 makes the IR remember them. |
| **Scope** | The HTML viewer only. `inlined.txt` and `domino inline` (story 03) keep their current plain output — they have no per-path context. |
| **Verdicts** | Unchanged. This is presentation plus one new serialised field per path. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The listing and its labels (story 02, `src/debug/ir.rs`)

- A `Label` is a **1-based line number in `Listing::text`** (`ir.rs:67`); labelling and rendering
  are one pass (`emit`, `:379`) and `sites: BTreeMap<Label, SiteInfo>` (`:177`) is 1:1 with the
  labelled lines.
- **Not every emitted line gets a label.** `emit` returns one, but these call sites throw it
  away:
  - `render_stmt`'s `if`: the `}` after the then-block, or `} else {` … `}` (`ir.rs:592-596`);
  - `render_call`: the `{` after the call line (`:673`), one `param <- arg;` line per argument
    (`:690`), and the closing `}` (`:700`).
  Those lines are executed and today cannot be painted. A synthetic `assert` is one line and its
  abort **re-uses the assert's label** (`:566-573`) — there is no separate abort row.
- Every `InlStmt` variant already carries `label`.

### 2.2 The executor (story 05/08, `src/debug/exec.rs`)

- `walk` (`:622`) is a single loop over a stack of `Cursor` frames with one `match` over
  `InlStmt` (`:646`); both children of a fork recurse through `descend` so each has a matching
  `BranchOracle::leave` scope (see the comment at `:613` — do not restructure it).
- `SymState` carries `steps: Vec<Step>` and is `clone()`d at every fork; `Step` is
  `{ label, decision }` (`:97`). `TerminalPath` (`:156`) is what `on_path` sees.
- `BranchOracle` (story 08) reports pruned children; the driver turns those into `PrunedBranch`.

### 2.3 The trace and the viewer (stories 06, 07, 13)

- `LeftPath` (`driver.rs:345`), `RightPath` (`:363`), `PrunedBranch` (`:255`), `StepView`
  (`:377`), `TerminalView` (`:386`), `SiteView` (`:301`). `TRACE_SCHEMA` is **6** (`:172`).
- `report.rs`: `listingBlock` (`:734`), `sec` (`:756`, `<details>` + `localStorage`, story 13),
  `listingMeta` (`:820`), `renderDetail` (`:942`), CSS custom properties at `:284` with a
  `prefers-color-scheme: dark` block at `:297`, listing CSS at `:486-497`.
- Determinism: two runs of an unchanged project produce byte-identical `trace.json` **and**
  `index.html`. Nothing added here may depend on wall-clock or `HashMap` order.

## 3. Work to do

### 3.1 `ir.rs` — remember the structural lines

Keep the labels `emit` already returns instead of discarding them:

```rust
InlStmt::Branch {
    label, cond, then, els, is_assert,
    /// Lines the *then* block occupies, inclusive, excluding the `if` line
    /// itself: `(first, last)` where `last` is the `}` or `} else {` row.
    /// `None` for a synthetic `assert` (one line, no block).
    then_lines: Option<(Label, Label)>,
    /// Likewise for the *else* block, `None` when there is no `else`.
    else_lines: Option<(Label, Label)>,
},
InlStmt::Call {
    label, frame, bind, body,
    /// `{`, the `param <- arg;` bindings and the closing `}` of the inlined
    /// frame: `(first, last)` — `first` is the `{`, `last` the `}`.
    frame_lines: (Label, Label),
    /// The argument-binding rows, `(first, last)`; `None` for a 0-arg oracle.
    arg_lines: Option<(Label, Label)>,
},
```

These are pure bookkeeping: the numbers exist already, they are simply dropped today. Do **not**
add sites for them — `sites` stays 1:1 with real statements, and every existing consumer
(`stepsTable`, `domino inline`, the snapshot in `testdata/story03`) keeps working unchanged.

### 3.2 `exec.rs` — record what was walked

- Add `visited: Vec<Label>` to `SymState`, cloned at forks like `steps`.
- In `walk`'s match, push the lines that control actually passed:
  - `Assign` / `Sample` / `Unwrap` / `Branch` / `Return` / `Abort`: their `label`;
  - `Call`: the `label`, then the `{`, then the argument rows — before descending into the body;
  - on entering a branch child, the child block's `(first, last)` **delimiter** rows: the `{` is
    part of the `if` line, so this is the `}` / `} else {` / `}` that close it;
  - a frame's closing `}` when the frame's cursor is popped, and a branch block's closing row
    when that block is entered. **Rule: a delimiter is painted iff its block was entered**, even
    when the block was left early through a `return` — it closes a region that did run.
- At `emit_terminal`, compress `visited` into sorted, deduplicated, merged inclusive ranges and
  store them on `TerminalPath`:

  ```rust
  /// Inclusive `(first, last)` line ranges of the listing this path executed,
  /// sorted and non-overlapping. Includes the block delimiters of entered
  /// blocks and the terminal line; excludes every untaken branch.
  pub lines: Vec<(Label, Label)>,
  ```
- The same compression is applied to the prefix reported for a pruned branch, so story 08's
  `PrunedBranch` can be painted up to its cut.

Write the compression once (`fn ranges(labels: &mut Vec<Label>) -> Vec<(Label, Label)>`) and unit
test it directly: empty, singleton, adjacent (`3,4,5` → `(3,5)`), gapped, out-of-order,
duplicated.

### 3.3 `driver.rs` — carry it into the trace

- `LeftPath`, `RightPath` and `PrunedBranch` each gain
  `pub lines: Vec<[usize; 2]>` (serialised as `[[3,9],[12,12]]` — arrays, not objects, for size).
- Bump `TRACE_SCHEMA` to **7**.
- `render_tree` is untouched (story 17 moves it to `summary.txt`; do not restyle it here).

### 3.4 `report.rs` — the CSS

Add tokens next to the existing ones (`:284` and the dark block at `:297`):

```css
--exec-bg: #eaf7ee;   /* light green: this line ran            */
--exec-edge: #bfe3ca; /* left rule on an executed row          */
/* dark: --exec-bg: #17251b;  --exec-edge: #2c4634;            */
```

and the row rules, replacing `.row.hi` / `.row.term`:

| Class | Meaning | Style |
|---|---|---|
| `.row.exec` | executed | `background: var(--exec-bg)`, 3px `--exec-edge` left rule |
| `.row.ret` | terminal `return` | `background: var(--ok-bg)`, 3px `--ok-fg` left rule |
| `.row.abort` | terminal `abort` | `background: var(--fail-bg)`, 3px `--fail-fg` left rule |
| `.row.cut` | a pruned branch's cut line | `background: var(--amber-bg)`, 3px `--amber-fg` left rule |
| (none) | not executed | unchanged — plain background |

Rows keep their current line-number gutter; the left rule replaces the gutter's border so the
listing does not shift width when a row is painted. `.row.abort` wins over `.row.exec` (a
failing `assert` is both), and `.ret`/`.abort` win over `.exec`.

### 3.5 `report.rs` — the painting

Change the signature to take the path, not just its steps:

```js
// `path` is a LeftPath / RightPath / PrunedBranch: { lines, steps, terminal, decision? }
function listingBlock(text, path, terminal) { … }
```

- Build the painted set from `path.lines`: for each `[a, b]`, rows `a..=b` get `exec`.
- The terminal row gets `ret` or `abort` from `terminal.is_abort`; for a `PrunedBranch`, the cut
  row (`pb.label`) gets `cut` instead and nothing after it is painted.
- Decision tags: from `path.steps`, `label → decision`; append
  `<span class="dtag">then</span>` (muted, right-aligned, `--fg-muted`, never selectable into a
  copy of the code — put it after the code span and give it `user-select: none`).
- Keep story 13's behaviour of centring the terminal row when the section opens
  (`pre._termRow`), and keep the whole listing in the DOM (`Ctrl-F` inside an open section).
- `listingMeta` becomes `312 lines · 41 executed` (count from `lines`, not `steps`).
- Add a one-line **legend** under the section summary of each listing:
  `executed · return · abort · not executed`, each word in its own colour chip. One shared
  `legend()` helper, used by both listings.

Nothing else in `renderDetail` moves: the section order, defaults and `localStorage` keys from
story 13 stay exactly as they are.

## 4. Acceptance criteria

- [ ] For `example-projects/hello-world` (medium ↔ small, `UsefulOracle`), the painted set of the
      single left path equals the whole oracle body **including** the inlined frame's `{`, its
      argument rows and its `}` — asserted in a unit test against the literal expected ranges.
- [ ] For a project with a real `if` (`example-projects/simple-KEM-example`, and `PKENC` in
      `kem-dem`), **no** line inside the untaken block is painted, on either side, for every path
      in the run (property test over the whole `trace.json`: for each path, every painted line is
      a line the executor recorded, and no painted line lies strictly inside an untaken block).
- [ ] A path ending in `abort` paints its body green and its abort row red; a path ending in
      `return` paints its return row in the stronger green. A failing `assert` row is red, not
      green.
- [ ] Selecting a pruned branch paints the prefix green and the cut row amber; nothing below the
      cut is painted.
- [ ] Branch rows show their decision tag inline; the tag text matches the `Path — left/right`
      table for the same label, and copying the listing text does not pick the tags up.
- [ ] `lines` is present on every `LeftPath` / `RightPath` / `PrunedBranch` in `trace.json`, is
      sorted, non-overlapping, and contains the terminal label; `TRACE_SCHEMA` is 7.
- [ ] `trace.json` grows by less than ~10% on `kem-dem` `PKENC` (record the before/after byte
      sizes in the implementation report).
- [ ] `sites` is still 1:1 with labelled statements; `testdata/story03/inline-hello-world.txt` is
      byte-unchanged and `domino inline` output is byte-unchanged.
- [ ] `index.html` for an unchanged project is byte-identical across two runs, still opens from
      `file://` with the network off, and still makes no requests.
- [ ] Readable in both light and dark (`prefers-color-scheme`), and the green/red pair is
      distinguishable in a red-green-blind simulation — that is what the left rules are for; do
      not ship colour as the only signal.
- [ ] `cargo build`/`test`/`clippy --workspace` clean, and with `--features cvc5-lib`.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
D=$PWD/target/debug/domino

cd example-projects/hello-world && $D debug --proof Proof --proofstep 0 \
    --oracle UsefulOracle --claim same-output && xdg-open _build/debug/*/*/*/*/index.html

cd ../kem-dem/kem-dem-cca-ssp
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
xdg-open $O/index.html     # pick a path with an if: check the untaken block is uncoloured

# an abort path, to see red
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC --claim same-output

# determinism
$D debug … --oracle PKGEN --claim same-output && cp $O/../../PKGEN/same-output/index.html /tmp/a.html
$D debug … --oracle PKGEN --claim same-output && diff /tmp/a.html $O/../../PKGEN/same-output/index.html
```

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release` (a bare `--release` never
> relinks the `domino` binary).

## 6. Notes / risks

- **The template is a Rust string literal** (`const TEMPLATE: &str = r##"…"##`). Keep the `r##`
  delimiters; a `"#` sequence inside the JS ends it.
- **Do not reconstruct structure in JS.** Brace matching over the rendered text looks tempting and
  breaks on the first `}` inside a string or comment. The executor knows; make it say so.
- **`assert` shares its label with its abort** (`ir.rs:566`). The colour precedence in §3.4 is the
  whole handling; there is no second row to paint.
- **Loop-unrolled code** produces distinct lines per iteration (`loopunroll` runs before
  `inline_oracle`), so a label never repeats within a path — the range compression may assume
  that, but keep the `dedup` anyway, it is one call.
- **Size.** If `lines` measurably bloats `trace.json` on a big run, the fallback is to drop
  ranges fully contained in an enclosing range, not to move the computation into JS.
- **Do not widen scope.** No syntax highlighting, no diffing of the two listings, no per-line SSA
  values on hover, no changes to `inlined.txt`.

## 7. State handed to the next story

Record in `docs/stories/16-…-IMPLEMENTATION-REPORT.md`: the new IR fields, the `visited`/`lines`
representation and its compression rule, the delimiter-painting rule as implemented, the CSS
tokens and class precedence, `TRACE_SCHEMA` 7, the `trace.json` size before/after on `PKENC`, and
screenshots of a return path, an abort path and a pruned branch.
