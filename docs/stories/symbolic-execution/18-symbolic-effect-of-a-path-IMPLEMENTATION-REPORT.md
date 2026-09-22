# Story 18 — Implementation report: symbolic return value & new state in the viewer

**Status:** done, uncommitted (per the owner's instruction — commit message at the bottom).
**Branch:** `amir/symbolic-execution-debugger`
**Builds/tests/clippy:** clean with and without `--features cvc5-lib`, incl. `--all-targets`.

---

## 1. `TRACE_SCHEMA`

**7 → 8.** It was `7` (story 16). Story 18 lands next and bumps by one.
`docs/stories/14` and `docs/stories/15` "Inherited" notes updated to say `8` and to
record the new `effect` fields.

## 2. What was built

A new module `src/debug/effect.rs` that unfolds a returning path's flat SSA
definitions back to the roots (oracle arguments, `old.<inst>.<field>`, package
consts, sample points) and pretty-prints the result. Every returning
`TerminalPath` / `LeftPath` / `RightPath` now carries an `effect`, serialised into
`trace.json`, rendered by a new **open-by-default** viewer section
`Effect — return value & new state`.

Nothing computed here is asserted; no verdict depends on it (proven below: the
`trace.json` diff is empty once `effect` and `schema` are removed).

## 3. `PathEffect` — field layout as implemented

`src/debug/effect.rs` (all `#[derive(Debug, Clone, Serialize)]`):

```rust
pub struct PathEffect {
    pub returns: Option<String>,   // None => `return` with no value; the whole struct is None for an abort
    pub state:   Vec<PkgEffect>,   // one per folded pkg instance, game-declaration order
    pub rand:    Vec<RandEffect>,  // sample points whose counter advanced, sample-id order
    pub wheres:  Vec<Binding>,     // hoisted shared sub-terms, dependency order
    pub truncated: bool,
}
pub struct PkgEffect  { pub pkg_inst: String, pub changed: Vec<FieldEffect>, pub unchanged: Vec<String> }
pub struct FieldEffect{ pub field: String, pub value: String, pub table: Option<TableUpdate> }
pub struct TableUpdate{ pub base: String, pub entries: Vec<Entry> }
pub struct Entry      { pub key: String, pub value: String }
pub struct RandEffect { pub point: String, pub ty: String, pub draws: usize }  // point = "I.O.sname"
pub struct Binding    { pub name: String, pub value: String }
```

### Serialised position

`TerminalPath.effect: Option<PathEffect>` — immediately after `terminal`, before
`reported_decls` (`src/debug/exec.rs`).
`LeftPath.effect` / `RightPath.effect: Option<PathEffect>` — immediately after
`terminal`, before `lines` (`src/debug/driver.rs`). `PrunedBranch` gains nothing
(a prune never reaches a terminal).

## 4. Thresholds — final values and why

| const | value | why |
|---|---:|---|
| `INLINE_MAX_CHARS` | **12** | keeps `old.Prot.ctr` (exactly 12 chars, 4 uses) inline while `encaps(old.Prot.pk, rand#0).1` (13+ chars) is hoisted. Matches the story's worked example and both goldens verbatim. |
| `MAX_TERM_CHARS` | **2000** | per-rendered-string cap; on overflow the string is cut with `…` and `truncated` set. |
| `MAX_WHERES` | **40** | cap on hoisted bindings; on overflow `truncated` is set and further terms inline. |
| `MAX_DEPTH` | **400** (private) | **added, not in the story.** The renderer/counter recurse over `SmtExpr`; a unit test built a 1000-deep `+` chain and blew the 2 MB test stack. At depth 400 (the whole corpus nests < 30) the term is cut with `…` and `truncated` set — never a panic, never an abort. |

## 5. The renderer (`effect::build`)

Two passes over a `HashMap<String, SmtExpr>` definition map (`<v!…>` name → rhs):

1. **count** — walk every root, bump a reach-count per SSA name, descend into a
   name's definition only the first time it is reached ("stop at an
   already-counted name, then bump it").
2. **render** — an SSA reference is **hoisted** into `wheres` iff reached ≥ 2
   times *and* its own rendering is > `INLINE_MAX_CHARS`; otherwise inlined.
   Bare sample draws (`__sample-rand-…`) are **always** named `basename#i` and
   spelled out in a `where` line. Hoist names are the SSA basename, disambiguated
   `x#2`, `x#3` on collision.

### Rewrite rules that were missing from §3.3's table

The story's table was complete for the two goldens. Extras added while wiring it:

- **`(* a b …)`** — `a * b` (only `+` / `-` were listed; PKENC has no `*` but a
  future oracle might).
- **`and` / `or` wrap in parens** — `(a && b)` not `a && b`, so nesting under a
  larger term stays unambiguous.
- **`(as const (Array …)) mk-none)`** with a *compound* head — handled before the
  atom-head dispatch, since `items[0]` is itself a `List`.
- **`<<func-NAME>>` → `NAME`** — the generic fallback strips `<`/`>` *and* a
  leading `func-`, so `(<<func-encaps>> …)` renders `encaps(…)` while an unknown
  `<<something>>` still renders `something(…)`.
- Generic 1-arg application renders as the bare name (no `()`), which is what
  makes `unwrap(old.P.sk)` come out right when it is itself the whole term.

### Term shapes that fell back to `head(args…)`

None on the acceptance projects. The fallback is exercised by
`effect::tests::unknown_head_degrades` (`<weird-new-op>` → `weird-new-op(x, 3)`).
`kgen`, `dem_enc`, `kem_encaps`, `decaps`, `encaps` all arrive as `<<func-…>>`
and render as `name(args)` via the same path — deliberately, not a fallback.

### `c_#2` in the wild

On `kem-dem` PKENC the right side returns `(c_, c_#2)` — two distinct SSA
constants both named `c_` in source, both hoisted, disambiguated. Ugly but
truthful and deterministic, exactly as the story's `ctxt#2` rule intends.

## 6. Building it — `exec.rs`

- `Executor` gains `state_seeds: HashMap<(String,String), String>` (final-vs-seed
  comparison for "unchanged") and `effect_roots: HashMap<String, String>` (seed
  SSA name → rendered root). Both are filled in `initial_state` for arguments,
  every folded package-state field (`old.{inst}.{field}`), and every *referenced*
  package const.
- `Executor::build_effect(&st, &terminal)` rebuilds the definition map from
  `st.constraints` (first `(assert (= <v!…> rhs))` per name wins — path
  conditions of the shape `(= <v!…> …)` never shadow, because the real
  definition is always pushed first), assembles the roots and calls
  `effect::build`. Called from `emit_terminal` **before** the `rebind_gs`
  game-state bookkeeping — that chain carries nothing the effect needs.
- The definition map is **rebuilt at the terminal**, never carried in `SymState`
  (which is cloned at every fork). Confirmed no PKENC regression (§8).

## 7. The viewer (`report.rs`)

New section appended in `renderDetail` **after `Path — right`, before
`Claim assertion`** — `detail.appendChild(effectSec(lp, isRight ? rp : null))`.

- `effectSec` builds a `.eff-grid` (two `1fr` columns, collapsing to one below
  900px via `@media`). A right-path selection fills both columns headed by the
  game-instance names; a left selection fills the left column only.
- Each column: `returns` (mono box), `new state` (one sub-block per package
  instance — changed fields as `field` + wrapping `<code>` value, a wide table
  gets one entry per line; then a dimmed `unchanged: …` line), `randomness`
  (`point +draws`, omitted when the path drew nothing), `where` (dimmed
  `name = value`, omitted when empty), and a dimmed truncation note when
  `truncated`.
- An abort column (effect `null`) reads `aborts at L<n> — no return value` and
  nothing else.
- `sec-meta`: one side → `returns 1 value · 5 of 8 fields changed`; two sides →
  `left: 5/8 · right: 5/8`.
- New CSS is all `eff-`-prefixed and reuses the existing dimmed / inset / border
  tokens — no new colours, legible in both themes. Open/closed state persists
  under `localStorage["domino.debug.sec.Effect — return value & new state"]` like
  every other `sec`.
- A dimmed footer in the body: *"a display derived from the path SMT — when in
  doubt, SMT asserted is authoritative"* (story §6).

Story 16's listing-painting in `renderDetail` is untouched; the two sections
coexist and the §3.6 order is kept.

## 8. Acceptance evidence

Measured on `example-projects/kem-dem/kem-dem-cca-ssp` `PKENC` / `same-output`,
baseline = branch tip `564e637b` rebuilt with `--workspace --features cvc5-lib`:

| | baseline (schema 7) | story 18 (schema 8) |
|---|---:|---:|
| `trace.json` | 713 676 B | 721 702 B (**+1.1 %**, ≪ 2×) |
| `summary.txt` | — | **byte-identical** (modulo the elapsed-time token) |
| verdicts | 4 left / 2 right / 2 verified | identical |
| wall clock | ~1.1 s | ~1.05 s (no regression) |
| `trace.json` with `schema` + `effect` removed | — | **byte-identical to baseline** |

- `simple-KEM-example` `Run` right path `#2.1`: every table field reads
  `old.<inst>.<field>[<key> -> <value>]` — no `<v!…>`, no `<pkg-state-…>`, no
  `store`, no `mk-some` (asserted in `golden_simple_kem_run_right_partner`).
  Matches the story's §3.7 golden verbatim (the `el3-i` / `mk-tuple3` round-trip
  through the inlined `ENC_and_DEC` is reduced away; `Corr_KEM` wholly unchanged).
- `simple-KEM-example` `Run` left `#2`: matches the §3.7 golden verbatim
  (`testdata/story18/simple_kem_run_left2.txt`).
- `kem-dem` PKENC left `#1`: `m1` appears as a bare oracle-argument name, and the
  stateless package instances (`Scheme_KEM` / `Scheme_DEM` / `Scheme_PKE`) render
  as empty state blocks without crashing
  (`testdata/story18/kem_dem_pkenc_left1.txt`).
- Aborts: `PKDEC` / `equal-aborts` — all 3 abort left paths have `effect: null`,
  the 1 returning path has an effect (`trace_carries_an_effect_for_every_returning_path`,
  plus a `python3` spot check).
- No panics: `debug` run over `simple-KEM-example` (both games), all of
  `kem-dem-cca-ssp` (`PKGEN`/`PKENC`/`PKDEC` × `same-output`/`equal-aborts`/`invariant`),
  `hello-world-oracle-rename`, and `kem-dem-cca-blended-parallel` proofsteps
  0/2/4. See §10 for one pre-existing failure surfaced (not caused) by that sweep.

## 9. Tests added

- `src/debug/effect.rs` — 14 unit tests over hand-built definition maps: store
  chains (single / nested / repeated key / `{}` base / `None` delete),
  `mk-some` stripping in value position, `el3-i` of `mk-tuple3` reduction,
  root / arg / const passthrough, sample inline-vs-`where`, the exact hoist
  threshold (13 hoisted, 12 inline), name-collision `x#2`, `MAX_DEPTH`
  truncation without panic, unknown-head degradation, `unchanged` verbatim.
- `src/debug/exec.rs` — `effect_is_none_for_abort_terminals`,
  `unchanged_fields_are_not_expanded`, `golden_simple_kem_run_left_2`,
  `golden_simple_kem_run_right_partner`, `golden_kem_dem_pkenc_left_1`
  (goldens in `testdata/story18/`, plus "no forbidden raw form leaks" assertions).
  A test-only `render_effect_fixture` helper produces the plain-text shape; it is
  not a product surface.
- `src/debug/driver.rs` — `trace_carries_an_effect_for_every_returning_path`
  (every return has an effect, every abort `null`, schema is 8, `trace.json`
  byte-identical across two runs).
- `src/debug/report.rs` — `synthetic_run` grows a `demo_effect()` on one left and
  one right path; `html_is_self_contained_and_embeds_the_trace` asserts the
  section title and a rendered `->` table update appear in `index.html`.
- Two hard-coded `assert_eq!(parsed["schema"], 7)` in `report.rs` and two in
  `driver.rs` bumped to `8`.

## 10. Notes for follow-up

- **Pre-existing, not caused here:** `domino debug --proof
  kem_dem_cca_blended_parallel --proofstep 4 --oracle PKENC` fails during solver
  setup with `Symbol 'get-rand-ctr-H3' not declared as a variable` — before any
  effect rendering. This is a base-frame / SMT-emission bug for that blended
  proofstep (cf. the "pre-existing blended-project test failures" noted in the
  story-04 report), unrelated to story 18.
- Empty state blocks for stateless folded package instances are rendered (name
  only). Harmless and truthful; a future story could suppress them.
- `MAX_DEPTH` is a safety valve, not a feature. If a real oracle ever nests
  deeper than 400 the effect for that path degrades to `…` + `truncated`; the
  `SMT asserted` section stays exact.
- Aborts still get no effect block (owner's decision). `build_effect` is
  terminal-agnostic apart from the early `return None` — wiring aborts on later
  is that one line plus a viewer tweak.

## 11. Commit message

```
Story 18: symbolic return value & new state per path in the debug viewer

`domino debug` could say which lines a path ran and what SMT it asserted, but
not what the path actually computes or leaves in the game state — the one
question a human asks first at a failing (left, right) pair. Answering it by
hand off the flat SSA transcript is exactly the work the debugger exists to
remove, and it had to be redone for every pair.

New module `src/debug/effect.rs` unfolds a returning path's flat, acyclic,
single-assignment SMT back to its roots — the oracle's arguments, the old game
state (`old.<inst>.<field>`), the game constants and the sample points — and
pretty-prints the result: table writes as `T[k -> v, k2 -> v2]`, shared
sub-terms hoisted into a `where` list, unchanged fields named on one line. It
is a two-pass renderer (reference-count, then render + hoist) with hard caps on
string length, `where` count and recursion depth; every unrecognised term still
renders as `head(args…)` rather than panicking. Purely a display — nothing it
produces is ever asserted and no verdict depends on it.

- `TerminalPath` / `LeftPath` / `RightPath` gain `effect: Option<PathEffect>`
  (immediately after `terminal`; `None` for an abort). Built in
  `exec.rs::emit_terminal` from the terminal's own `SymState`, before the
  game-state bookkeeping — pure and side-effect free (story 14 builds it per
  worker unchanged).
- `Executor` gains `state_seeds` / `effect_roots`, filled in `initial_state`.
- Viewer: a new open-by-default `Effect — return value & new state` section,
  appended after `Path — right` and before `Claim assertion`. A right-path
  selection shows left and right side by side (two columns, collapsing to one
  below 900px); a left selection shows the left column only. All-new CSS is
  `eff-`-prefixed and reuses existing tokens — legible in both themes.
- `TRACE_SCHEMA` 7 → 8. `trace.json` on `kem-dem` PKENC grows 1.1 % and is
  byte-identical to before once `schema` and `effect` are removed; `summary.txt`,
  the stdout tree, the `smt/` files, verdicts, path/prune counts and wall-clock
  are unchanged.

Tests: 14 unit tests in `effect.rs`, five executor tests (three goldens under
`testdata/story18/`), one driver test (every returning path has an effect,
aborts `null`, `trace.json` deterministic), and a report assertion that the
section and a rendered table update reach `index.html`.

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01M1qt1yAvh79BL9WYRjbjQn
```
