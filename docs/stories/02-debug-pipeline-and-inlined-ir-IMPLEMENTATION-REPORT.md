# Story 02 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. Not yet committed.

Read together with `docs/stories/02-debug-pipeline-and-inlined-ir.md`. This is the "State handed to
the next story" for **stories 03 and 05** (and 06, transitively).

`cargo build --workspace && cargo test --workspace` both pass (98 lib tests, incl. 6 new
`debug::ir::tests::*`). No changes to `EquivalenceTransform` behaviour — the shared pipeline helper
is exercised by the existing `src/parser/tests/complete` suite.

---

## 1. What landed

| File | Change |
|---|---|
| `src/transforms/theorem_transforms.rs` | New `pub struct DebugTransform` next to `EquivalenceTransform`. Both now call the shared `fn transform_game_inst_common(game_inst, run_treeify: bool)`. `treeify` is the *only* difference and is now a single `if run_treeify { … }` step. Same `Err` (`EquivalenceTransformError`) and same `Aux` (`Vec<(String, GameInstAux)>`). |
| `src/debug/mod.rs` | **new.** `pub mod ir;` + module docs. |
| `src/debug/ir.rs` | **new.** The inlined IR + `inline_oracle` + one-pass labeller/renderer + 6 unit tests (~1100 lines incl. docs). |
| `src/lib.rs` | `pub mod debug;` (before `pub mod expressions;`). |

Nothing else was touched.

## 2. `DebugTransform` — public surface (stories 05/06)

```rust
// src/transforms/theorem_transforms::DebugTransform
impl TheoremTransform for DebugTransform {
    type Err = EquivalenceTransformError;          // identical to EquivalenceTransform
    type Aux = Vec<(String, GameInstAux)>;         // identical to EquivalenceTransform
}
```

Pipeline (in `transform_game_inst_common`, `run_treeify = false`):

```
type_extract → deconstructinvoke → unwrapify → resolveoracles → samplify → loopunroll →
sample_max_counter_extractor → returnify → tableinitialize
```

i.e. `EquivalenceTransform` minus `treeify`. The `GameInstAux { types, sample_info, max_offsets }`
is byte-for-byte what `EquivalenceTransform` produces (everything that feeds the aux runs before
the treeify step), so story 06 can hand a `DebugTransform` result straight to
`EquivalenceContext::new` and every `emit_*` in `writers/smt/contexts/equivalence/emit.rs` keeps
working.

## 3. The IR — public surface (stories 03/05)

`crate::debug::ir::{ InlinedOracle, InlBlock, InlStmt, Place, VarKey, FrameInfo, Listing,
SiteInfo, SiteKind, Label, MAX_INLINE_DEPTH, inline_oracle, InlineError }`

```rust
pub fn inline_oracle(game_inst: &GameInstance, oracle_name: &str)
    -> Result<InlinedOracle, InlineError>;
```

- `game_inst` **must** already be a `DebugTransform` output.
- `oracle_name` is the **exported** name (matched against `Export::name()`).

Types are exactly as spec'd in the story §3.2, **with two deviations** (see §5):

1. `Place` gained a `Tuple(Vec<Place>)` variant.
2. `InlStmt::Sample` / `InlStmt::Unwrap` carry the fields the story listed; `sample_name` is
   `String` (empty when the source had no `sample-name`).

`InlineError` variants: `OracleNotExported`, `CalleeNotFound`, `MaxDepthExceeded`,
`UnresolvedEdge` (the last is "treat as a bug and say so" per the story).

### Labels / listing

`Label` = 1-based line number into `listing.text`. The labeller **is** the renderer (one pass).
Every `InlStmt` occupies its own line and gets `label = that line`; structural lines (`{`,
`} else {`, `}`, the two header lines, and the per-frame argument-binding lines) get no label and
no `SiteInfo`. `listing.sites: BTreeMap<Label, SiteInfo>` has one entry per labelled `InlStmt`
(exception: `assert`, see §5).

Rendering rules implemented (kept close to `amir/ty-params-features:src/inline.rs` so story 03's
side-by-side stays familiar — the whole expr/type/pattern renderer is ported from there):

```
// game instance: <gi>   (package instance: <pi>, package: <pkg>)
<SIG> {
    <stmt lines…>
}
```

- `assert (c)`  → one line `assert (<c>);`, `SiteKind::Assert`,
  `InlStmt::Branch { is_assert: true, then: [], els: [Abort] }`.
- unwrap assign → `x <- unwrap(<inner>);`, `SiteKind::Unwrap`, `InlStmt::Unwrap`.
- sample        → `x <-$ <ty>[ sample-name <n>];`, `SiteKind::Sample`.
- `if`          → `if (<c>) {` … `} else {` … `}` (else block omitted if empty).
- `invoke`      → call line `<bind> <- invoke <name>(<args>)      // <PkgInst>.<Oracle>`
  (discard form: `invoke <name>(<args>)      // …`), then `{`, then arg-binding lines
  `<param> <- <caller-arg-expr>;`, then the nested body, then `}`.
- `return` inside a frame → `<bind> <- <expr>;  // return from <PkgInst>.<Oracle>`
  (`<bind>` is `_` for a discarded invoke; `<expr>` is `()` for a bare `return;`).
- `return` at the entry frame → `return <expr>;` / `return;`.

## 4. Alpha-renaming / locals-vs-state (story 05 mirrors this exactly)

- `frame_id` is allocated in **DFS pre-order** as calls are rendered; entry frame is `0`. The
  listing (and hence every label) is byte-identical across runs — verified by a test.
- **Locals** — `Identifier::Generated`, `PackageIdentifier::Local`, `PackageIdentifier::OracleArg`
  — are rewritten to `Identifier::Generated("{pkg_inst}#{frame_id}::{name}", ty)` inside every
  expression (via `Expression::map`), and become `Place::Local { key, ty }` with the same key when
  used as an assignment target.
  - **Entry-oracle arguments** live under `"{entry_pkg_inst}#0::{arg_name}"`. `InlinedOracle.args`
    keeps the bare `(name, ty)` from the exported signature — story 05/06 must bind those under the
    frame-0 keys.
- **Package state** — `PackageIdentifier::State` — is **not** renamed. In expressions it stays a
  `State` identifier; as a target it becomes
  `Place::State { pkg_inst, field, ty }` where `pkg_inst = state_ident.pkg_inst_name` (falls back
  to `pkg_name` if unset — it is always set post-instantiation) and `field = state_ident.name`.
  Keyed globally by `(pkg_inst, field)`.
- **Constants** (`PackageIdentifier::Const`, `GameIdentifier::*`, `TheoremIdentifier::*`) are left
  untouched in the IR expressions so the SMT they generate still matches the prover's. (The text
  renderer *does* follow `Const` → `game_assignment` / `assigned_value` chains down to a literal or
  theorem const, purely for readability — that only affects `listing.text`, never the IR.)

## 5. Decisions not written in the story (the story asked for these to be recorded)

1. **`Place::Tuple(Vec<Place>)` — new variant.** Tuple patterns *do* reach the IR: `deconstructinvoke`
   turns `(a,b) <- invoke O()` into `_invoke-result-N <- invoke O()` **plus** `(a,b) <- _invoke-result-N`,
   and that second statement is a plain `AssignmentRhs::Expression` with a `Pattern::Tuple`.
   (`test-splitinvoke` hits this on both sides.) The story's `Place` enum had no way to express it
   and the AST has no tuple-projection expression to desugar into, so I added `Place::Tuple`.
   **Story 05:** evaluate the RHS to a tuple value and bind component-wise; a nested `Tuple` /
   `Discard` / `Index` element is possible in principle (only flat `Ident` lists occur in the
   current corpus).

2. **`assert` and its synthetic `Abort` share a line/label.** `assert (c)` renders as *one* line.
   The `InlStmt::Branch { is_assert: true }` it produces has `els = [InlStmt::Abort { label }]`
   with `label` == the assert's own label, and only **one** `SiteInfo` (kind `Assert`) is recorded
   for that label. So for an oracle containing asserts, "every `listing.sites` key is used by
   exactly one `InlStmt`" is *not* literally true (the Branch and its inner Abort share it); the
   acceptance test checks that property only on `hello-world` `UsefulOracle`, which has no asserts.
   Story 05 should treat the `els` Abort of an `is_assert` Branch as "the `fails` decision" and not
   expect a distinct line for it.

3. **`Pattern::Table` targets inside frames.** Rendered as `ident[idx]`; IR is
   `Place::Index { base: <place of ident>, index: <idx rewritten into the frame> }`. `base` is
   whatever `ident` resolves to — `Local` for a frame-local table, `State` for a package-state
   table. No test project exercises a *state* table write inside an inlined frame, but the code
   path is symmetric with the local case.

4. **Argument-binding lines are unlabelled.** They are not `InlStmt`s (they live in
   `FrameInfo.arg_bindings` for the executor), so they get a listing line but no `Label` / `SiteInfo`.
   They render with the **bare** callee parameter name (`m0 <- <expr>;`) even though the value is a
   frame-local keyed `{callee_pkg}#{frame_id}::m0` — matches the reference inliner. The rewritten
   RHS expression in `arg_bindings` is in the **caller's** namespace.

5. **`Expression::map` gaps.** `borrow_map` (and `mapfold`, used by `unwrapify`) `panic!` on
   `Neg/Inv/Pow/Mod/Concat/Sum/Prod/Any/All/Union/Cut/SetDiff` and `Sample`-typed sub-exprs never
   occur here. This is a pre-existing repo limitation shared with `unwrapify`; none of the test /
   example projects contain those operators in oracle code, so `rewrite_expr` is fine in practice.
   If a future project hits it, the fix is to fill in the missing arms in `src/expressions.rs`.

6. **Text renderer is a near-verbatim port** of `amir/ty-params-features:src/inline.rs`
   (`render_expr` / `render_type` / `render_countspec` / `render_pattern` / `ident_repr` /
   `resolve_const` / `render_bare_ident`). Kept as free functions in `ir.rs`. Double-parenthesised
   output like `assert (not ((x == None)));` is inherited from that port and is intentional (stable
   > pretty).

7. **`SiteInfo.span`** is the originating `Statement`'s `file_pos()` (for `if`/`assert`,
   `IfThenElse::full_span`). It is **not** remapped through inlining — it always points into the
   package source file the statement was written in.

## 6. Tests (`src/debug/ir.rs`, module `tests`)

| test | project | checks |
|---|---|---|
| `hello_world_labels_are_distinct_lines_and_sites_are_1to1` | `example-projects/hello-world` `small_composition` / `UsefulOracle` | every `InlStmt` label is a distinct line in range; `listing.sites` keys == `InlStmt` labels |
| `hello_world_medium_inlines_a_nested_call` | `hello-world` `medium_composition` / `UsefulOracle` | `InlStmt::Call` with non-empty nested `body`, `frame.pkg_inst_name == "rand"` |
| `splitinvoke_call_body_is_nested_and_in_callee_instance` | `test-projects/test-splitinvoke` `game_split` / `Query` | nested non-empty `Call.body`, `frame.pkg_inst_name == "pair"`, `bind.is_some()` |
| `loopunroll_has_no_loops_and_is_stable` | `test-projects/test-loopunroll` `B` / `Test` | listing byte-identical across two runs; body was unrolled |
| `kem_dem_pkenc_has_assert_and_unwrap` | `example-projects/kem-dem/kem-dem-cca-ssp` `Game_MON_CCA_PKE` / `PKENC` | ≥2 `is_assert` Branches each with `els == [Abort]`; ≥1 `InlStmt::Unwrap` |
| `snapshot_hello_world_small_useful_oracle` | `hello-world` `small_composition` / `UsefulOracle` | exact `listing.text` string |

Test helper `with_debug_theorem(dir, theorem_name, f)` loads a real project directory
(`DirectoryFiles::load` + `DirectoryProject::load`), runs `DebugTransform`, hands `f` the theorem.
CWD for `cargo test` is the `sspverif` crate root (repo root), so the relative paths resolve.

`kem-dem-cca-ssp` is used as a unit-test fixture — safe because we only parse + transform + inline,
never invoke a solver. (`4WHS` / `yao` are still never touched.)

## 7. Follow-ups / notes

- No `domino inline` CLI yet — that is story 03, which re-uses `listing.text` verbatim and only
  adds line numbers + the side-by-side split.
- `MAX_INLINE_DEPTH` is `pub const` in `ir.rs` if story 03 wants to surface it.
- The `_ <- ();  // return from …` rendering for a discarded void invoke is a bit awkward; story 03
  may want to prettify it in the CLI layer without changing the IR.
