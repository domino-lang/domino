# Story 08 — Lowering EasyCrypt to the debugger IR, and `domino inline --easycrypt`

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 03 (package modules), story 04 (routers).
**Blocks:** 09.

---

## 1. Why this story exists

The owner wants the symbolic debugger to work on the **generated EasyCrypt code**, not on Domino
code:

> Note that debugger UI should inline the generated Easycrypt code to really help a user working on
> the EasyCrypt to match the proof and remaining admits to the EasyCrypt code. Domino syntax should
> be forgotten at this point.

The settled approach (overview §3): the EasyCrypt AST is the artifact, and a **lowering** turns
inlined EasyCrypt code into the debugger's existing IR, so executor, solver, claims, HTML and
`trace.json` stay untouched. This story builds the lowering and exposes it through
`domino inline --easycrypt`. Story 09 runs the solver on it.

## 2. Inherited from earlier stories

### 2.1 The debugger IR (`src/debug/ir.rs`, epic `docs/stories/00-overview.md`)

```rust
pub type Label = usize;      // 1-based line number in Listing::text — the single source of truth
pub struct InlinedOracle { game_inst_name, oracle_name, entry_pkg_inst,
                           args: Vec<(String, Type)>, return_type: Type,
                           body: InlBlock, listing: Listing }
pub enum InlStmt { Assign { label, target: Place, rhs: Expression },
                   Sample { label, target, sample_id, ty, sample_name },
                   Unwrap { label, target, inner },          // branch point: none => abort
                   Branch { label, cond, then, els, is_assert, then_lines, else_lines },
                   Call   { label, frame: FrameInfo, bind, body, frame_lines, arg_lines },
                   Return { label, value }, Abort { label } }
pub enum Place { Local { key: VarKey, ty }, State { pkg_inst, field, ty },
                 Index { base, index }, Tuple(Vec<Place>), Discard }
pub struct Listing { text: String, sites: BTreeMap<Label, SiteInfo> }
pub fn inline_oracle(game_inst: &GameInstance, oracle_name: &str) -> Result<InlinedOracle, InlineError>;
```

`sites` is 1:1 with labelled statements. Story 16 of the debugger epic added `then_lines`,
`else_lines`, `frame_lines` and `arg_lines` so the viewer can paint entered blocks — the lowering
must fill them for EasyCrypt listings too.

### 2.2 Rendering helpers

`src/debug/render.rs`: `columns(left, right, line_numbers)`, `render_side_by_side(…)`,
`RenderError`. `domino inline` is `Commands::Inline` in `crates/domino/src/cli.rs` with
`--project`, `--proof`, `--proofstep`, `--oracle` and a no-line-numbers flag.

### 2.3 From stories 03 and 04

The generated module bodies and the router's shape:
`if (!abort_flag) { ec_r <@ Inst_X.o(args); if (ec_r = None) { abort_flag <- true; } }`, packages
returning options, `ec_result`/`ec_r<N>` temporaries, and the continuation-nesting shape for
`Unwrap`/invoke (story 03 §3.5).

### 2.4 From story 17 (added by the story 17 session)

Read `16-easycryptify-IMPLEMENTATION-REPORT.md` and `17-unwrap-temporaries-IMPLEMENTATION-REPORT.md`
first: stories 16–17 replaced the §2.3 continuation-nesting shape. The facts that bear on the
lowering:

- **There are no `unwrap_N` temporaries in exported code any more.** `Unwrap(e)` now appears
  *inside* other expressions: conditions (`if (d_First.[oget sid] = None)`), table indices, call
  arguments (`O.d_ENC(oget pk, m1)`), tuple right-hand sides, and nested in another unwrap's
  operand (`d_State.[oget d_First.[sid]]`). Every such `oget e` sits inside the then-branch of an
  `if (!(e = None))`, and `easycryptify` asserts that (`every_unwrap_is_guarded`).
- `src/writers/smt/expr_expr.rs` now lowers an `Unwrap` *inside* an expression to
  `(maybe-get e)` instead of panicking, so the executor can run the easycryptified code. That is
  EasyCrypt's `oget`: total, with an unspecified value on `None`. A whole-right-hand-side
  `x <- Unwrap(e)` still becomes an `InlStmt::Unwrap` fork. Its `unwrap-none` child is infeasible,
  because the guard dominates it.
- On a Domino listing (`DebugTransform`, no `--easycrypt`) nothing changed: `unwrapify` still
  hoists every unwrap into an `unwrap-N` binding there.

## 3. Work to do

New file `src/writers/easycrypt/lower.rs`.

### 3.1 What "inlining EasyCrypt" means here

Produce, for one exported oracle of one game instance, an `InlinedOracle` whose `listing.text` is
**EasyCrypt source** — the router procedure with every package call inlined in place, exactly as
story 04/03 would have rendered them, plus the frame braces and argument bindings that
`inline_oracle` emits for Domino. The entry point is the router proc; each `EcStmt::Call` becomes
an `InlStmt::Call` frame whose body is the callee procedure's lowered body.

```rust
pub fn inline_oracle_ec(game_inst: &GameInstance, oracle_name: &str)
    -> Result<InlinedOracle, EcExportError>;
```

Mirror `inline_oracle`'s structure (frame ids, `MAX_INLINE_DEPTH`, alpha-renaming into
`"{pkg_inst}#{frame}::{name}"` keys) so that everything downstream behaves identically.

### 3.2 The provenance rule — read this twice

The executor encodes `Place` and `Expression` into SMT through the **existing Domino machinery**,
and the claims come from `EquivalenceContext`, which is built from the Domino game. So the lowered
IR must denote **the same state and the same values** as the Domino game does. Concretely:

- A module variable that came from a Domino package state field lowers to
  `Place::State { pkg_inst, field, ty }` with the **Domino** instance and field names — not the
  mangled EasyCrypt ones. The mangled name appears only in `listing.text`.
- A procedure local lowers to `Place::Local` with a frame-scoped key, as today.
- Expressions lower to the **Domino** `Expression` they were translated from. Keep the Domino
  expression alongside the EasyCrypt one during export (a side table from `EcExpr` identity to the
  originating `Expression`, or simply carry both in the lowering input); do **not** try to translate
  EasyCrypt expressions back into Domino.
- The router's `abort_flag` has no Domino counterpart. It is *not* a state place: an oracle that
  reaches the `ec_r = None` branch is exactly a Domino abort, so lower that branch to
  `InlStmt::Abort` and drop the flag assignment. Likewise the outer `if (!abort_flag)` guard is
  dropped — the debugger already models "this oracle call happens".
- `ec_result` is not a place either: `ec_result <- Some e` lowers to `InlStmt::Return { value: e }`,
  and a path that never assigns it lowers to `InlStmt::Abort`.
- Story 03's nested `if (x = None) { } else { … }` for `Unwrap` lowers back to `InlStmt::Unwrap`
  (decisions `some`/`none`), and the invoke form lowers to `InlStmt::Call` — so path counts match
  the Domino side except for `treeify`'s duplication.

**The consequence to accept up front:** because the export pipeline runs `treeify` and the debug
pipeline does not, an EasyCrypt listing has *more* syntactic paths than the Domino listing for the
same oracle. That is expected and was accepted when the export pipeline was chosen (overview §3).
Verdicts must still agree; story 09 asserts that.

### 3.3 Labels and the listing

- `Label` stays a 1-based line number into `listing.text`, now EasyCrypt text.
- `sites` stays 1:1 with labelled statements; fill `then_lines` / `else_lines` / `frame_lines` /
  `arg_lines` exactly as `ir.rs` documents, so story 16's painting works unchanged.
- Render through story 01's renderer — never `format!` EasyCrypt syntax here.

### 3.4 `domino inline --easycrypt`

Add the flag to `Commands::Inline`. With it, both sides' listings are the EasyCrypt ones; without
it, behaviour is byte-identical to today. Reuse `render::columns` for the side-by-side output.

## 4. Acceptance criteria

- [ ] `domino inline --easycrypt --proof <T> --proofstep 0 --oracle <O>` prints EasyCrypt code for
      both sides of `example-projects/hello-world` and `example-projects/kem-dem/kem-dem-cca-ssp`.
- [ ] Golden files under `testdata/easycrypt/story08/` for `hello-world` (`UsefulOracle`) and
      `kem-dem` (`PKENC`), and `domino inline` **without** the flag is byte-unchanged
      (`testdata/story03/inline-hello-world.txt` still matches).
- [ ] The listing text, extracted from the IR, is accepted by `easycrypt compile` when wrapped in a
      minimal procedure — i.e. the inlined body is real EasyCrypt, not pseudo-code. (Skip when
      `easycrypt` is absent.)
- [ ] Unit tests assert the provenance rule: for `kem-dem` `PKENC`, every `Place::State` in the
      lowered IR has a `pkg_inst`/`field` pair that exists in the Domino game, and every `Return`
      value expression is the Domino expression from the corresponding Domino IR node.
- [ ] A path that aborts through the router's `ec_r = None` branch ends in `InlStmt::Abort`, with no
      `abort_flag` assignment anywhere in the IR.
- [ ] `then_lines`/`else_lines`/`frame_lines`/`arg_lines` are populated; `sites` is 1:1 with
      labelled statements.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean, including `--features cvc5-lib`.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/hello-world && $D inline --easycrypt --proof Proof --proofstep 0 --oracle UsefulOracle
cd ../kem-dem/kem-dem-cca-ssp && $D inline --easycrypt --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC
```

> Never run `inline`/`debug` against `example-projects/4WHS` or `yao`.

## 6. Notes / risks

- **Do not re-parse EasyCrypt.** Nothing here reads `.ec` text; the lowering consumes the AST the
  exporter built.
- **Do not change `src/debug/ir.rs`'s semantics.** Adding a constructor is fine; changing what
  `Place::State` means would break `domino debug` for Domino listings.
- **`treeify` duplication is visible to the user** as repeated code in the listing. That is the
  honest picture of what the EasyCrypt proof looks like; do not collapse it.
- **Frame keys must stay unique** across the duplicated branches `treeify` produced, or two distinct
  locals will alias in the DSA store.

## 7. State handed to the next story

Record in `08-…-IMPLEMENTATION-REPORT.md`: `inline_oracle_ec`'s signature, how provenance is
carried from export to lowering, the router/`ec_result` elimination rules as implemented, the
path-count difference vs the Domino listing for `PKENC` (numbers), and the golden-file paths.
