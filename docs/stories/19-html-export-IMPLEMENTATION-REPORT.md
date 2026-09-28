# Story 19 — implementation report: `domino html` (per-theorem proof viewer)

**Status:** done, ad hoc (no story spec preceded it). Branch `amir/symbolic-execution-debugger`.
**Not committed** — proposed commit messages at the bottom.

Built across two Claude Code sessions working in the same worktree, sometimes concurrently:

- **Session A** (`70c10513…`): the command, the page, the diagrams, lossy rendering,
  proposition paths, the package pane.
- **Session B** (`3c4c2f0d…`): made the export survive games whose loops `loopunroll` cannot
  unroll (the Yao example) — `ViewTransform`, `InlineError::NonUnrolledLoop`,
  `render_oracle_listing`.

Both sessions' changes were reviewed together for this report (§8).

`cargo build -p domino`, `cargo clippy -p sspverif -p domino` (0 warnings) and
`cargo test -p sspverif --lib` (157 passed, 4 ignored) are clean on the combined tree. The
`cvc5-lib`-gated tests were not run. `domino prove` / `debug` / `inline` / `latex` output is
unchanged (§6).

---

## 1. Concept

A proof in Domino is a chain of game hops, and the question one keeps asking while writing it is
"what does oracle `O` actually do in game `G_i`, next to `G_{i+1}`?". Answering that by hand means
opening several `.comp.ssp` and `.pkg.ssp` files and following `invoke`s across packages.

`domino html` writes **one self-contained HTML page per theorem** that answers it directly:

```
┌ theorem Full4WHS          [lossy] [wrap lines] [A− A+] [packages]  ←/→ previous / next game
│ [main  Real ~ Ideal]  [other proposition …]                    ← one tab per proposition
│ Real → equivalence → H1_0 [b ↦ false] → reduction → H1_1 …    ← the path, clickable
├──────────┬──────────────────────────────┬──────────────────────────────┬──
│          │ 1/27 Real [b -> false]       │ 2/27 H1_0 [b -> b] [b ↦ false]│   game header
│          │ game H0                      │ game H1 · via equivalence …  │
│          │ b=0                          │ b=0                          │   game bits
│          │ ┌────┐   ┌─────┐             │ ┌────┐   ┌─────┐   ┌───────┐ │   composition
│          │→│KX⁰ │ → │Prot │             │→│KX⁰ │ → │Prot │ → │Nonces⁰│ │   diagram
├──────────┼──────────────────────────────┼──────────────────────────────┼──
│ NewKey   │ NewKey(ltk: …) -> Integer {  │ NewKey(ltk: …) -> Integer {  │   one row per
│          │   …fully inlined…            │   …fully inlined…            │   exported oracle
│ Send1    │ …                            │ …                            │
```

- **Columns are the games of a proposition, in proof order.** For each proposition
  (`propositions { name: Left ~ Right }`) the page shows the path the proof assembler
  (`Proof::try_new`, a BFS over the game hops with constant specialization) found from `Left` to
  `Right`. Each column is one step of that path, with the hop that led to it. The same game can
  appear more than once with different specializations (e.g. 4WHS goes `H1_0 [b ↦ false] … H1_0
  [b ↦ true]`). A theorem without propositions gets one tab listing its hops' games instead.
- **Rows are exported oracles.** Each cell is the oracle inlined across package boundaries —
  the same listing `domino inline` prints, minus its `// game instance:` header line. A game
  that doesn't export the row's oracle gets an empty cell.
- **Each column header is the game's composition diagram**, drawn with the same z3 layout the
  LaTeX export uses for its tikz figures.
- **Parameters are visible where they matter**:
  - The header lists the game instance's Boolean constants as the theorem sets them,
    `[bit1 -> true, bit2 -> b]`. Proof parameters (theorem constants) are in red, followed by
    the red `[b ↦ false]` the path fixes them to.
  - A caption above the diagram shows the resolved bits, `bit1=1 bit2=0`.
  - Each package box is labelled with the **package** name, with its Boolean parameters as a
    superscript (`KX_NoKeys⁰`). The **instance** name goes underneath in parentheses when it
    differs.
- **Clicking a package** opens a side pane with the instance's parameters
  (`name: Type = value`, specialization applied) and the package's full source, highlighted.

## 2. What landed

| File | Change | Session |
|---|---|---|
| `src/writers/html.rs` (new, 1060 lines) | The page: tabs, grid, SVG diagrams, package pane, CSS, JS. | A (+B: `ViewTransform`, `render_oracle_listing`) |
| `src/writers/mod.rs` | `pub mod html;` | A |
| `crates/domino/src/cli.rs` | `Html` subcommand and args. | A |
| `crates/domino/src/main.rs` | `html()` dispatch; `Error::Transform`, `Error::Io(PathBuf, io::Error)`. | A |
| `src/debug/ir.rs` | Lossy rendering (`inline_oracle_rendered`, `render_expr_with`, `Inliner::lossy`); `render_expr` made `pub(crate)`. View-mode loops (`render_oracle_listing`, `Inliner::render_loops`), `InlineError::NonUnrolledLoop` replacing an `unreachable!`, `Inliner::game_inst_name` removed. | A, B |
| `src/proof.rs` | `Proof::path()`; `ConstAssignment` made `pub` with `original_name()` / `assigned_value()`. | A |
| `src/transforms/theorem_transforms.rs` | `ViewTransform`; `run_treeify: bool` → `PipelineOptions { run_treeify, require_max_offsets }` with `EQUIVALENCE` / `DEBUG` / `VIEW` presets. | B |
| `src/debug/{driver,effect,exec,progress,render,report,smtout}.rs`, `src/writers/smt/contexts/equivalence/emit.rs` | **Formatting only** (`cargo fmt`). Verified: `rustfmt(HEAD version) == staged version` for each. | — |

No `Cargo.toml` / `Cargo.lock` change. The page loads nothing external: no CDN, no fonts, no
network.

## 3. Command

```
domino html [--path P] [--proof T] [--out DIR] [-s z3 | --no-solver] [--lossy]
```

| Flag | Meaning |
|---|---|
| `--path` | Project root; default: search upward for `ssp.toml`. |
| `--proof T` | Only theorem `T` (else every theorem). Unknown name → `TheoremNotFound`. |
| `--out DIR` | Default `<project>/_build/html/`. Writes `<theorem>.html` and prints each path. |
| `-s/--smtsolver` | Layout solver, default `z3` (same default as `domino latex`). |
| `--no-solver` | Use the solver-free fallback layout. |
| `--lossy` | Open the page in lossy mode. Both renderings are always embedded. |

Not behind `cvc5-lib`: layout goes through the process solver backend, and `--no-solver` needs
none at all.

## 4. Pipeline

```
Theorem (untransformed)
 ├─ ViewTransform ─────────────► theorem_view   (for listings)
 ├─ theorem.proofs → Proof::path() + game_hops()  (for columns / hops / specialization)
 └─ theorem.instances           (for headers, diagrams, parameters — generic, untransformed)

per tab, per step:   header  ← GameInstance.consts (Bool), ConstAssignment pairs
                     diagram ← GraphLayout(z3) | fallback  +  PackageInstance params
per oracle row:      cell    ← render_oracle_listing(theorem_view[game], oracle, lossy∈{f,t})
                               cached per (game instance, oracle)
```

### 4.1 Columns — `tabs()`

`Proof` already stores what the proof assembler found: `sequence` (indices into its
specialization table) and `hops`. `Proof::path()` exposes
`(&GameInstance, &[ConstAssignment])` per step, where the assignment list is what the step's
specialization fixed (e.g. `b: b->false`). `game_hops()` yields one hop per consecutive pair.

The specialized `GameInstance` in the path has literal consts but a composition that was **not**
re-instantiated. So the column uses the *generic* instance of the same name from
`theorem.instances` for everything it renders, and carries the assignments separately as
`(theorem const name, literal)` pairs. They are deduplicated: two game constants set from the
same theorem constant produce the same pair twice (4WHS `H6_0`).

This shows the path the search **found** (BFS shortest), not the order it explored games in.

### 4.2 Listings

`render_oracle_listing(inst, oracle, lossy)` returns only the listing text of the debug inliner
(no IR; §5). `strip_header` drops the first line when it starts with `// game instance:`, since
the column header says the same. Both renderings are generated once per `(game, oracle)` —
a game can occur on several paths — and embedded as `<pre class="full">` /
`<pre class="lossy">`. The page toggles them with a body class.

**Lossy** matches the LaTeX export's `lossy` (`src/writers/tex/writer/block.rs`):
`Some(x)` → `x`, `unwrap(x)` → `x` (also the `x <- unwrap(y)` statement), `None` → `⊥`,
`EmptyTable(T)` → `EmptyTable`, and `not (a == b)` → `(a != b)`. Only text changes: the IR and
the line labels of `inline_oracle_rendered(.., true)` are identical to the non-lossy call.
`inline_oracle` = `inline_oracle_rendered(.., false)`, so `domino debug` / `domino inline`
listings are byte-identical to before (the story-03 snapshot test still passes).

### 4.3 Diagrams — `diagram_svg`

`solver_geometry` reads the same model variables `tikzgraph.rs::smt_composition_graph` does
(`{pkg}-column/top/bottom`, `edge-{a}-{b}-height`, `edge---{b}-height`, `--column`) and uses its
geometry: column pitch 3.5, box width 2, heights halved. These tikz units are scaled by 50 px,
y-flipped, and emitted as inline SVG — boxes, horizontal arrows with a marker head, and the
oracle names stacked above each arrow. The layout cache is `_build/graph/`, **the same directory
`domino latex` uses**, so the two share cached layouts.

`fallback_geometry` (no solver, or unsat): column = longest call depth from the adversary
(bounded relaxation, so cycles terminate), boxes stacked per column, arrows horizontal at the
callee's centre. Crossings are possible; it is only a fallback.

Package node (`package_node`): an SVG `<g class="pkgnode">` holding the box, the package name
with a superscript of its Boolean parameter values (`true`→1, `false`→0, else the rendered
expression after substituting the path's assignments), and the `(instance)` line when it
differs. Text that would overflow gets `textLength` + `lengthAdjust`. `data-pkg`, `data-inst`
and `data-params` feed the side pane. A `<title>` gives the hover tooltip.

### 4.4 Game bits

`game_bits(game)`: the composition's `Bool` consts in declaration order, each looked up in
`GameInstance.consts`. `is_param` is true when the value is a
`TheoremIdentifier::Const` — a proof parameter. The header shows `[name -> value]` in normal
weight with parameters in red. `bits_caption` shows `name=digit` with parameters resolved
through the path's assignments.

### 4.5 Page behaviour (inline JS, ~150 lines)

- **Layout.** The body is a 100vh flex column. The grid scroller fills the rest of the
  viewport, so its horizontal scrollbar is always on screen. The game-name row and the
  oracle-name column are sticky.
- **Navigation.** Path chips jump to their column and are highlighted while that column is
  visible (computed on scroll via rAF). `←`/`→` step one column. `scroll-snap-type: x
  proximity`, with `scroll-padding-left` set to the sticky column's width.
- **Options.** Lossy, wrap (80ch), code font size (8–20 px) and last tab are remembered in
  `localStorage`. Every access is wrapped in `try/catch`, and the page works without it.
- **Package pane.** A fixed right drawer (`min(680px, 50vw)`). The grid gets a matching right
  margin instead of being covered. Package sources are embedded once per package in hidden
  `<pre class="pkgsrc">`, and a small tokenizer highlights keywords and `//` / `/* */`
  comments. Close with ×, `Esc` or the toolbar button.
- **Theming.** Light and dark via `prefers-color-scheme` custom properties.

## 5. Loops `loopunroll` cannot unroll (session B)

**Symptom:** `domino html` on `example-projects/yao` failed with
`domino::sample_max_counter::unbounded_loop` for oracle `GARBLE`, although `domino prove` passes.

**Cause:** `prove` transforms only the instances in equivalence / hybrid hops. The games that
contain `GARBLE` (`Mod`, `Mod3Layer`, loops `for j: 1 <= j <= w`) appear only in reduction hops.
The HTML export transforms *every* instance, and `sample_max_counter_extractor` rejects loops
whose bounds are symbolic theorem constants.

**Fix, in two steps:**

1. `ViewTransform` — the `DebugTransform` pipeline with `require_max_offsets: false`. When the
   extractor fails, the instance keeps its composition and gets empty `max_offsets`. Views never
   build a randomness mapping, so nothing reads them. `EquivalenceTransform` / `DebugTransform`
   are unchanged: both presets keep `require_max_offsets: true`, and `EQUIVALENCE` alone keeps
   `run_treeify: true`.
2. The debug IR had `unreachable!` for a surviving `Statement::For`. It is now
   `Err(InlineError::NonUnrolledLoop { oracle, pkg_inst })` for `inline_oracle*` (debug and
   inline keep rejecting such loops). For views, `render_oracle_listing` sets
   `Inliner::render_loops`. The loop is printed as `for j: lo <= j <= hi { … }` around its
   inlined body, nested calls included. The body's IR is spliced in as if it ran once, which is
   wrong, so `render_oracle_listing` returns only the `Listing` and never the IR.

Result: all four yao pages render, and `GARBLE` shows its loops (15 and 43 `for j:` blocks in
`Yao.html` / `Yao3Layer.html`) with no error cells.

## 6. Unchanged behaviour

- `inline_oracle(g, o)` ≡ `inline_oracle_rendered(g, o, false)`. `render_expr` ≡
  `render_expr_with(_, false)`. The `Inliner` output is unchanged unless `lossy` or
  `render_loops` is set.
- `EquivalenceTransform` / `DebugTransform` pipelines are unchanged (§5.1).
- `Proof` gained only accessors; its search is untouched.
- The eight formatting-only files have no semantic change (checked by re-formatting their
  HEAD versions and comparing).

## 7. Verification

| Check | Result |
|---|---|
| `cargo clippy -p sspverif -p domino` | 0 warnings |
| `cargo test -p sspverif --lib` | 157 passed, 4 ignored (incl. story-03 `inline` snapshot) |
| `domino html` (z3), debug build | 4WHS 5.5 s (2 pages, 27 + 8 columns), yao 1.7 s (4 pages), kem-dem-cca-ssp, simple-KEM-example, hello-world < 0.3 s — all without error cells |
| Headless Chrome | No console errors. Screenshots checked: path tabs, lossy view, wrapped view, diagrams with superscripts / instance lines / bit caption, package pane opened by a synthetic click. |
| Page sizes | 25 KB (hello-world) … 918 KB (Full4WHS, both renderings × 27 columns) |

Not verified: real keyboard / mouse interaction (only a synthetic click), the `cvc5-lib` tests.
`nprf` and `hello-world-hybrid` fail to *load* (pre-existing type / theorem errors), so they were
not exercised.

## 8. Review notes and known limitations

1. **Listings are not specialized.** A column for `H1_0 [b ↦ false]` inlines the generic
   `H1_0`: code still reads `b`. Headers, captions, superscripts and pane parameters *are*
   substituted. Fixing this needs re-instantiating the specialized game (`GameInstance::new`
   with the original `Composition`), which `Proof` doesn't keep.
2. **`ViewTransform` tolerates every extractor error**, not only `unbounded_loop`
   (`Err(_) if !opts.require_max_offsets`). Harmless today, since views ignore `max_offsets`,
   but matching the specific variant would be stricter.
3. **The `render_loops` IR is wrong by construction** (the body is spliced once). It is only
   safe because `render_oracle_listing` discards it; the field's doc says so. Do not return
   `InlinedOracle` from a `render_loops = true` run.
4. **Path, not exploration order.** Columns follow the path `Proof::try_new` returned. If the
   BFS exploration order is ever wanted, `try_new` would have to record it.
5. **Page size** grows with columns × oracles × 2 renderings. Full4WHS is ~0.9 MB. Rendering
   lossy on demand in JS would halve it, but would need the IR in the page.
6. **No automated tests for `html.rs`.** A snapshot of `hello-world` with `--no-solver`
   (deterministic) would pin the markup. The lossy renderer also has no unit test yet.
7. **Stale module doc.** `html.rs`'s header comment still says cells are "the same listing
   `domino inline` prints". It is now that listing without the header line and with symbolic
   loops printed. Worth a one-line touch-up.
8. The layout cache is keyed by composition name (existing `GraphLayout` behaviour), shared with
   `domino latex`. The HTML output directory `_build/html/` is git-ignored with the rest of
   `_build/`.

## 9. Proposed commit message

The index currently holds the feature **and** eight formatting-only files. I suggest two
commits so the feature diff stays reviewable:

```
FMT="src/debug/driver.rs src/debug/effect.rs src/debug/exec.rs src/debug/progress.rs \
     src/debug/render.rs src/debug/report.rs src/debug/smtout.rs \
     src/writers/smt/contexts/equivalence/emit.rs"
git restore --staged $FMT
git add docs/stories/19-html-export-IMPLEMENTATION-REPORT.md
git commit            # feature message below
git add $FMT
git commit            # formatting message below
```

Messages:

**Formatting commit**

```
cargo fmt the debugger modules

Formatting only: rustfmt of the HEAD versions of src/debug/{driver,
effect,exec,progress,render,report,smtout}.rs and
src/writers/smt/contexts/equivalence/emit.rs is byte-identical to this
commit.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
```

**Feature commit**

```
Story 19: `domino html` — per-theorem proof viewer

Adds `domino html [--proof T] [--out DIR] [-s z3 | --no-solver] [--lossy]`,
writing one self-contained HTML page per theorem to _build/html/:

- one tab per proposition; its columns are the games on the path
  Proof::try_new found from left to right, with the hop between each pair
  and the constants the path specializes (`[b ↦ false]`)
- one row per exported oracle, each cell the oracle inlined across
  packages (full or lossy, toggled in the page)
- a composition diagram on top of each column, drawn as SVG from the same
  z3 layout as the LaTeX tikz export (shared _build/graph cache), with a
  solver-free fallback; boxes show the package name, Boolean parameters as
  a superscript and the instance name when it differs
- the game's Boolean constants in the header (proof parameters marked)
  and as `bit=0/1` above the diagram
- a side pane with the package source and instance parameters on click;
  column chips, ←/→ navigation, wrap and font-size options

Supporting changes:
- ir.rs: lossy rendering (`inline_oracle_rendered`, `render_expr_with`)
  matching the LaTeX lossy export; `inline_oracle` output is unchanged.
  `render_oracle_listing` prints loops with symbolic bounds as `for`
  blocks for views; `inline_oracle*` now return
  `InlineError::NonUnrolledLoop` for them instead of panicking.
- theorem_transforms.rs: `ViewTransform` (the debug pipeline tolerating
  sampling loops loopunroll cannot unroll, e.g. Yao's GARBLE);
  `run_treeify` became `PipelineOptions` with one preset per transform.
  Equivalence/Debug pipelines are unchanged.
- proof.rs: `Proof::path()` and public `ConstAssignment` accessors.

Report: docs/stories/19-html-export-IMPLEMENTATION-REPORT.md

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
```
