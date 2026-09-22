# Story 02 — Debug transform pipeline + labelled inlined-oracle IR

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** nothing. Can be done in parallel with stories 01 and 04.
**Blocks:** stories 03 and 05.

---

## 1. Why this story exists

The debugger symbolically executes an exported oracle *as the reader sees it* — one flat piece of
code with all `invoke`s resolved into the callee's body — and reports execution paths as line
numbers into that rendering. So we need two things:

1. A transform pipeline that prepares game instances for symbolic execution. It must **not** run
   `treeify`.
2. An **AST-level** inlined representation of one exported oracle, with a stable label on every
   branch, assertion, unwrap, return and abort, produced together with the textual listing those
   labels index into.

### Why no `treeify`

`treeify` (`src/transforms/treeify.rs`) exists only so the SMT writer can emit `ite`: it takes a
block containing an `if` followed by more statements and pushes **all the trailing statements
into both branches**. That is pure duplication. For symbolic execution it is actively harmful —
it multiplies the number of syntactic paths, and it destroys the 1:1 relationship between a
statement in the source and a statement in the IR that the labels depend on. A symbolic executor
sequences naturally, so it does not need `ite`-shaped code at all.

### Why an AST-level inline and not the textual one

`src/inline.rs` on branch `amir/ty-params-features` inlines *while pretty-printing* — it produces
text, no AST. We need a structure the executor can walk. Do **not** port that module as-is;
re-implement it on top of the IR below (story 03 turns the IR back into the same side-by-side
text).

### The crux: `Call` stays nested

A callee can `return` from inside a branch. Flattening such a callee into the caller would
require duplicating the caller's continuation into every callee leaf — exactly what `treeify`
does, and exactly the blow-up we are avoiding. So the IR keeps a **`Call` node with the callee
body nested inside it**. The executor (story 05) treats a `Return` inside a frame as "bind the
call's result and continue after the `Call` node", using a frame stack. Zero duplication.

`abort` is different: it propagates. `smt_build_invoke` (`src/writers/smt/writer.rs:771`) makes a
callee abort abort the *whole* oracle, after writing the caller's locals back into the game
state. So `Abort` is always a global terminal, no matter how deep the frame.

## 2. What exists today

### Pipeline

`src/transforms/theorem_transforms.rs`:

```rust
pub struct EquivalenceTransform;                 // line 17
pub struct GameInstAux { pub types: HashSet<Type>,
                         pub sample_info: samplify::SampleInfo,
                         pub max_offsets: sample_max_counter_extractor::MaxOffsets }   // line 34

impl TheoremTransform for EquivalenceTransform { // line 40
    type Err = EquivalenceTransformError;
    type Aux = Vec<(String, GameInstAux)>;
    fn transform_theorem<'a>(&self, theorem: &'a Theorem<'a>)
        -> Result<(Theorem<'a>, Self::Aux), Self::Err>;
}

fn transform_game_inst(game_inst: &GameInstance)                                        // line 57
    -> Result<(GameInstance, (String, GameInstAux)), EquivalenceTransformError>
```

`transform_game_inst` runs, in order:
`type_extract → deconstructinvoke → unwrapify → resolveoracles → samplify → loopunroll →
sample_max_counter_extractor → returnify → treeify → tableinitialize`.

The comment at lines 65–78 explains the ordering constraints — read it, they still apply:
`samplify` must precede `loopunroll`; `sample_max_counter_extractor` must follow both
`loopunroll` and `resolveoracles`.

### AST

`src/statement.rs`:

```rust
pub struct CodeBlock(pub Vec<Statement>);

pub enum Statement {
    Abort(SourceSpan),
    Return(Option<Expression>, SourceSpan),
    Assignment(Assignment, SourceSpan),
    InvokeOracle(InvokeOracle),
    IfThenElse(IfThenElse),
    For(Identifier, Expression, Expression, CodeBlock, SourceSpan),   // gone after loopunroll
}

pub struct Assignment { pub(crate) pattern: Pattern, pub(crate) rhs: AssignmentRhs }
pub enum Pattern { Ident(Identifier), Table { ident, index }, Tuple(Vec<Identifier>) }
pub enum AssignmentRhs {
    Expression(Expression),
    Sample { ty: Type, sample_name: Option<String>, sample_id: Option<usize> },
    Invoke { oracle_name: String, args: Vec<Expression>, edge: Option<Edge>, return_type: Option<Type> },
}
pub struct InvokeOracle { pub oracle_name: String, pub args: Vec<Expression>,
                          pub edge: Option<Edge>, pub file_pos: SourceSpan }
pub struct IfThenElse { pub(crate) cond: Expression, pub(crate) then_block: CodeBlock,
                        pub(crate) else_block: CodeBlock, then_span, else_span, full_span }
```

### Facts you need

- **`assert (c)` is sugar** for `if (c) {} else { abort; }`: an `IfThenElse` with an empty
  `then_block` and an `else_block` of exactly one `Statement::Abort`. (The textual inliner on
  `amir/ty-params-features` detects it exactly this way.)
- **`unwrapify`** (`src/transforms/unwrapify.rs`) hoists nested `unwrap`s into assignments whose
  RHS is `ExpressionKind::Unwrap(inner)`. `src/writers/smt/writer.rs:899` compiles each into
  `if inner = (as mk-none (Maybe T)) then abort else <bind (maybe-get inner)>`. Those assignments
  are the unwrap branch points.
- **`deconstructinvoke`** already split `(a,b,c) <- invoke O(...)` into
  `_invoke-result-N <- invoke O(...)` followed by `(a,b,c) <- _invoke-result-N`, so an invoke's
  bind pattern is never a `Tuple`.
- **`resolveoracles`** fills in `Edge`. `Edge::to()` is an index into `Composition::pkgs`;
  `Edge::sig()` is the callee's `OracleSig`.
- **`returnify`** guarantees every oracle body ends in a `Return` or `Abort` (it errors with
  `MissingReturn` otherwise).
- **Package state vs locals.** In the existing encoding an oracle binds the package's state
  fields as *locals* on entry (`src/writers/smt/writer.rs:1032`), mutates them, and writes them
  back on return (`OracleContext::smt_write_back_state`). Before an `invoke`, `smt_build_invoke`
  writes the caller's locals back into the game state, so a re-entrant call sees the update. Our
  IR/executor gets the same semantics *for free* by keying package state on
  `(pkg_inst_name, field)` globally instead of per frame.
- `MAX_INLINE_DEPTH = 128` is the recursion bound the textual inliner used; keep the same idea.

## 3. Work to do

### 3.1 `DebugTransform`

Add to `src/transforms/theorem_transforms.rs`, next to `EquivalenceTransform`:

```rust
pub struct DebugTransform;

impl TheoremTransform for DebugTransform {
    type Err = EquivalenceTransformError;   // same error type; same failure mode (unbounded loop)
    type Aux = Vec<(String, GameInstAux)>;  // same aux, so emit.rs keeps working unchanged
    ...
}
```

Factor `transform_game_inst` into a shared helper parameterised by `run_treeify: bool` (or split
into `transform_game_inst_common` + a treeify step) so the two pipelines cannot drift. The debug
pipeline is:

`type_extract → deconstructinvoke → unwrapify → resolveoracles → samplify → loopunroll →
sample_max_counter_extractor → returnify → tableinitialize`

— identical to `EquivalenceTransform` minus `treeify`. Returning the same `GameInstAux` matters:
story 06 feeds the result to `EquivalenceContext::new`, and every `emit_*` function in
`src/writers/smt/contexts/equivalence/emit.rs` must keep working against it.

### 3.2 The inlined IR — new module `src/debug/ir.rs`

Create `src/debug/mod.rs` (declaring `pub mod ir;`) and wire it into `src/lib.rs`.

```rust
/// 1-based line number in the rendered listing. The listing is the single source of truth.
pub type Label = usize;

pub struct InlinedOracle {
    pub game_inst_name: String,
    pub oracle_name: String,       // the *exported* name
    pub entry_pkg_inst: String,
    pub args: Vec<(String, Type)>, // the exported signature's arguments
    pub return_type: Type,
    pub body: InlBlock,
    pub listing: Listing,
}

pub struct InlBlock(pub Vec<InlStmt>);

pub enum InlStmt {
    Assign { label: Label, target: Place, rhs: Expression },
    Sample { label: Label, target: Place, sample_id: usize, ty: Type, sample_name: String },
    /// Branch point: aborts when `inner` is none, otherwise binds `(maybe-get inner)`.
    Unwrap { label: Label, target: Place, inner: Expression },
    Branch { label: Label, cond: Expression, then: InlBlock, els: InlBlock, is_assert: bool },
    /// An inlined `invoke`. The callee body is NESTED, not flattened.
    Call   { label: Label, frame: FrameInfo, bind: Option<Place>, body: InlBlock },
    Return { label: Label, value: Option<Expression> },
    Abort  { label: Label },
}

pub enum Place {
    /// A frame-local variable (already alpha-renamed).
    Local { key: VarKey, ty: Type },
    /// A package state field. Shared across frames of the same package instance.
    State { pkg_inst: String, field: String, ty: Type },
    /// Table write: `T[index] <- ...` against either of the above.
    Index { base: Box<Place>, index: Expression },
    /// The `_` discard.
    Discard,
}

pub struct FrameInfo {
    pub frame_id: usize,
    pub pkg_inst_name: String,
    pub oracle_name: String,
    /// callee parameter -> caller-side argument expression, already rewritten into the
    /// caller's namespace. Bound as locals of the new frame on entry.
    pub arg_bindings: Vec<(VarKey, Type, Expression)>,
    pub return_type: Type,
}

/// Unique key for a frame-local. `format!("{pkg_inst}#{frame_id}::{name}")`.
pub type VarKey = String;

pub struct Listing {
    pub text: String,                       // the rendered code, one label per line
    pub sites: BTreeMap<Label, SiteInfo>,
}

pub struct SiteInfo {
    pub kind: SiteKind,                     // Assign | Sample | Unwrap | Branch | Assert | Call | Return | Abort
    pub line: String,                       // the rendered line, trimmed
    pub span: SourceSpan,                   // back-reference into the original source
    pub pkg_inst_name: String,
    pub oracle_name: String,
    pub depth: usize,
}
```

Entry point:

```rust
pub fn inline_oracle(
    game_inst: &GameInstance,      // already run through DebugTransform
    oracle_name: &str,             // the exported name
) -> Result<InlinedOracle, InlineError>;
```

Errors (mirror `amir/ty-params-features:src/inline.rs`): oracle not exported by the game
instance; callee definition not found; max inline depth exceeded; unresolved `Edge` (should be
impossible after `resolveoracles` — treat as a bug and say so).

### 3.3 Labelling and rendering are one pass

Labels are line numbers, so the labeller **is** the renderer. Walk the code once, emitting a line
per statement and recording `label = current_line_number` on the `InlStmt` and a `SiteInfo` in
`listing.sites`. Every `InlStmt` must have its own line; structural lines (a closing brace, a
frame header comment) get no label.

Suggested rendering (keep it close to the textual inliner on `amir/ty-params-features` so story
03's side-by-side output is familiar):

```
 1 | // game instance: Game_MON_CCA_PKE   (package instance: MON_CCA_PKE, package: MON_CCA_PKE)
 2 | PKENC(m: Bits(ptl)) -> Bits(dctl) {
 3 |     assert (pk != bot);
 4 |     if (b) {
 5 |         c <- invoke ENC(m)                      // Scheme_PKE.ENC
 6 |         {
 7 |             (dk, kc) <- kem_encaps(r, pk);
 8 |             dc <- dem_enc(dk, m);
 9 |             c <- (kc, dc);                      // return from Scheme_PKE.ENC
10 |         }
11 |     } else {
...
```

Rules:

- `assert (c)` is rendered as `assert (...)` and produces `Branch { is_assert: true }`; the
  decision names are `holds` / `fails` rather than `then` / `else`.
- An assignment whose RHS is `ExpressionKind::Unwrap(inner)` renders as
  `x <- unwrap(inner);` and produces `InlStmt::Unwrap`; decisions are `some` / `none`.
- An `invoke` renders as the call line (labelled, `SiteKind::Call`) followed by a braced block
  containing the argument bindings and the inlined body.
- A `Return` inside a frame renders as `<bind> <- <expr>;  // return from <Pkg>.<Oracle>` — the
  same convention the textual inliner used.

### 3.4 Alpha-renaming and the locals/state split

- **Locals** (oracle arguments and body-local variables) are renamed per frame to
  `"{pkg_inst}#{frame_id}::{name}"`, so two frames of the same package instance never collide.
  Rewrite every identifier occurrence in expressions with `Expression::map`
  (`src/expressions.rs:90`).
- **Package state fields** are *not* renamed and *not* frame-scoped. They become
  `Place::State { pkg_inst, field, ty }`, keyed globally. Identify them by
  `Identifier::PackageIdentifier(PackageIdentifier::State(..))` — the same identifier variant
  `PackageInstanceContext::smt_update_pkgstate_from_locals` constructs
  (`src/writers/smt/contexts/pkg_inst.rs:198`).
- **Package/game/theorem constants** are left alone; they resolve through the existing const
  machinery and must keep their identifiers so the SMT they generate matches the prover's.

### 3.5 Determinism

`frame_id` is assigned in traversal order; the listing must be byte-identical for an unchanged
project. Story 07 depends on that.

## 4. Acceptance criteria

- [ ] `DebugTransform` exists, shares its pipeline code with `EquivalenceTransform`, and differs
      only by omitting `treeify`. `EquivalenceTransform`'s behaviour is unchanged.
- [ ] `src/debug/ir.rs` exposes `InlinedOracle`, `InlBlock`, `InlStmt`, `Place`, `FrameInfo`,
      `Listing`, `SiteInfo`, `inline_oracle`.
- [ ] Unit test: for `example-projects/hello-world`, every `InlStmt`'s `label` indexes a distinct
      line of `listing.text`, and every `listing.sites` key is used by exactly one `InlStmt`.
- [ ] Unit test: an `assert (c)` in the source yields `Branch { is_assert: true }` whose
      `else` block is a single `Abort`.
- [ ] Unit test: an assignment with an `Unwrap` RHS yields `InlStmt::Unwrap`.
- [ ] Unit test on `test-projects/test-splitinvoke`: the inlined body contains at least one
      `InlStmt::Call` whose nested `body` is non-empty and whose `frame.pkg_inst_name` is the
      callee's package instance.
- [ ] Unit test on `test-projects/test-loopunroll`: the IR contains no loop construct (loops were
      unrolled) and the listing is stable across two runs.
- [ ] Snapshot test pinning `listing.text` for one small project, so accidental rendering changes
      are caught.
- [ ] `cargo build --workspace && cargo test --workspace` pass.

## 5. How to verify

```bash
cargo build --workspace
cargo test  --workspace

# once story 03 lands you can eyeball it; until then, print from a unit test:
cargo test --workspace -- --nocapture debug::ir
```

Test projects to use, in order: `test-projects/test-loopunroll`,
`test-projects/test-splitinvoke`, `example-projects/hello-world`, and — for the first realistic
shape — `example-projects/kem-dem/kem-dem-cca-ssp` (proofstep 0, oracles `PKGEN`/`PKENC`/`PKDEC`).

> **Never** run anything against `example-projects/4WHS` or `example-projects/yao`. They are the
> slow projects (`example-projects/known-good-slow.txt`) and will burn the session. See
> `docs/stories/00-overview.md` §7.

## 6. Notes / risks

- Watch out for `Statement::For` surviving into the IR — it must not, `loopunroll` runs before.
  Treat it as `unreachable!` with a message naming the game/package/oracle, in the style of
  `src/writers/smt/writer.rs:114`.
- `deconstructinvoke` means an invoke's bind is never a `Pattern::Tuple`; assert that rather than
  handling it.
- Do not try to make the IR generic over "split oracles" — that machinery is commented out
  throughout the codebase and is out of scope.

## 7. State handed to the next story

Stories 03 and 05 will rely on:

- `crate::transforms::theorem_transforms::DebugTransform` with
  `Aux = Vec<(String, GameInstAux)>` (same as `EquivalenceTransform`).
- `crate::debug::ir::{InlinedOracle, InlBlock, InlStmt, Place, VarKey, FrameInfo, Listing,
  SiteInfo, SiteKind, Label, inline_oracle, InlineError}`.
- The exact rendering rules above — story 03 re-uses `listing.text` verbatim and only adds line
  numbers and the side-by-side split.
- The locals/state split: `Place::Local` keyed by `"{pkg_inst}#{frame_id}::{name}"`,
  `Place::State` keyed by `(pkg_inst, field)` globally. Story 05's symbolic store mirrors this
  exactly.

Record here anything you had to decide that is not written above (e.g. how you handled
`Pattern::Table` targets inside inlined frames, or comment/`SourceSpan` quirks).

---

## 8. Implemented — see `02-debug-pipeline-and-inlined-ir-IMPLEMENTATION-REPORT.md`

**Status: done (uncommitted).** Full handover in that report; the decisions the section above
asked for, in brief:

1. **`Place` gained a `Tuple(Vec<Place>)` variant.** Tuple patterns reach the IR via
   `deconstructinvoke`'s `(a,b) <- _invoke-result-N` second statement (an `AssignmentRhs::Expression`,
   not an invoke). The AST has no tuple-projection expr to desugar into, so `Place::Tuple` it is.
   Story 05: eval RHS to a tuple, bind component-wise.
2. **`assert (c)` renders as one line**; its `InlStmt::Branch { is_assert: true }` has
   `els = [Abort { label }]` sharing the assert's label, with a single `SiteInfo` (kind `Assert`).
   So the "one `InlStmt` per `sites` key" invariant holds for assert-free oracles only; the
   acceptance test scopes itself to `hello-world` accordingly.
3. `Pattern::Table` target → `Place::Index { base: <Local|State>, index: <rewritten> }`.
4. Per-frame **argument-binding lines are unlabelled** (they live in `FrameInfo.arg_bindings`);
   they render with bare param names, RHS in the caller's namespace.
5. `Expression::map` still `panic!`s on `Neg/Inv/Pow/Mod/Concat/Sum/Prod/Any/All/Union/Cut/SetDiff`
   (pre-existing, shared with `unwrapify`); no corpus project hits it.
6. `SiteInfo.span` is the raw `Statement::file_pos()` — points into the package source, not remapped.
7. Text renderer (`render_expr`/`render_type`/`ident_repr`/`resolve_const`/…) is a near-verbatim
   port of `amir/ty-params-features:src/inline.rs`, kept as free fns in `src/debug/ir.rs`.
8. Entry-oracle args are frame-`0` locals keyed `"{entry_pkg_inst}#0::{arg_name}"`;
   `InlinedOracle.args` keeps the bare signature pairs.
