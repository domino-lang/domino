# Story 08 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (409 passed, 5 `#[ignore]`d:
the same 5 as after story 17, none failing) and `cargo clippy --workspace --all-targets` are clean.
`easycrypt` (`r2026.06-12-g7e192dd`) was on `PATH`, so the compile test ran for real. The ignored
story-16/17 differential test, `cargo test --workspace -- --ignored easycryptify_matches_treeify`,
still passes. **`--features cvc5-lib` could not be built in this environment:** `cvc5-sys` builds
cvc5 from source and its `configure.sh` fails with `cmake: command not found`. That is independent
of this story, and no `cvc5-lib`-gated code uses anything this story changed (§7).

## 0. The correction this story was implemented under

Story 08's text predates stories 16 and 17. It was implemented with this correction, supplied by
the supervising session and taken as authoritative:

- **The export pipeline runs `EasyCryptTransform` (`easycryptify`), not `treeify`.** Nothing is
  duplicated. Story 08 §3.2's paragraph "The consequence to accept up front: because the export
  pipeline runs treeify…" and §6's "`treeify` duplication is visible to the user" bullet were
  ignored. The same applies to §6's "frame keys must stay unique across the duplicated branches"
  (they are unique anyway, by frame id).
- **The writer's internals in §2.3 are gone.** `translate_block` is now a near-identity lowering of
  `easycryptify`'s output. The lowering follows the current `package.rs`/`game.rs` code, not
  story 08's prose.

Beyond that correction, these parts of story 08 were also found stale or wrong:

1. **§2.3 and §4's router shape.** The router is now
   `if (!abort_flag) { ec_result <@ Pkg_Inst_X.o(args); if (ec_result = None) { abort_flag <- true; } }`
   followed by `return ec_result`. There is no `ec_r`: "the router's `ec_r = None` branch" is its
   `ec_result = None` branch.
2. **§3.2, "Story 03's nested `if (x = None) { } else { … }` for `Unwrap` lowers back to
   `InlStmt::Unwrap`".** That shape no longer exists. The decision point for an unwrap is now
   `easycryptify`'s `if (!(e = None)) { … } else { ec_done <- true; }` guard, which is an
   `InlStmt::Branch`. The `x <- oget e` inside it is an `InlStmt::Assign` (§3.1). The supervisor's
   brief suggested that a whole-right-hand-side unwrap stays an `InlStmt::Unwrap`. This was
   deliberately not done, and §3.1 explains why.
3. **§3.2, "so path counts match the Domino side except for `treeify`'s duplication".** This is
   false, for a different reason. The EasyCrypt IR has *more* syntactic paths than the Domino IR:
   one infeasible child per inlined call that can return (§4). Verdicts must still agree.
4. **§3.2, "a side table from `EcExpr` identity to the originating `Expression`".** Not needed.
   The lowering takes story 08's other option, "carry both in the lowering input". It walks the
   easycryptified **Domino** body and has the writer translate each statement as it goes (§2).
5. **§3.1, "each `EcStmt::Call` becomes an `InlStmt::Call` frame".** This holds for
   package→package calls, but not for the router's own call. The entry package procedure is the
   entry frame, frame 0. This keeps `InlinedOracle::args`' documented keys
   (`"{entry_pkg_inst}#0::{arg}"`) and makes entry returns equal to the Domino ones (§2).
6. **Story 08 never mentions `ec_done`**, which is a story-16 construct. Its handling is in §2.
7. **§2.2 names `--project`.** `domino inline`'s flag is `--path`.
8. **Two doc comments in `ast.rs` anticipate this story.** `EcExpr::None_` keeps its `EcType` "because
   story 08's lowering needs the type of an abort value". `ProofLine::ByequivPrecondition` is kept
   structured "so story 08 has the actual relational formula". Neither turned out to be needed.
   The IR's abort is `InlStmt::Abort`, which has no value. The lowering does build one
   `None_(ty)`, for the router's `ec_result = None` line, but it gets that type from the Domino
   signature anyway. The comments are harmless and were left alone.

## 1. What changed

- **New `src/writers/easycrypt/lower.rs`** (plus `lower/tests.rs`, 13 tests). It defines
  `pub fn inline_oracle_ec(game_inst: &GameInstance, oracle_name: &str) -> Result<InlinedOracle,
  EcExportError>`.
- **`src/writers/easycrypt/package.rs`**, behaviour-preserving:
  - The oracle translator's identifier spelling is now pluggable through
    `pub(super) trait OracleNaming { expr, target }`. The module's own `PackageScope` implements it
    with bare names, exactly as before.
  - `translate_block`'s loop body became `translate_stmt`.
  - New `pub(super)` entry points: `translate_oracle_stmt`, `translate_oracle_expr`,
    `var_spelling` (the body of `var_name`), `ident_raw_name_and_type` and `SampleTemps` (the
    `ec_s<N>` counter and its declarations).
  - A table write's map operand now goes through `naming.expr` instead of `EcExpr::Var(name)`.
    This renders identically for the module.
- **`src/writers/easycrypt/game.rs`**, behaviour-preserving. New `pub(super)` helpers:
  - `instance_module_names(comp)`, the `Pkg_Inst_<inst>` names, now also used by
    `render_game_file`;
  - `router_module_and_flag(comp)`, which returns `Game_<Comp>` and `abort_flag`, with a new
    `ABORT_FLAG` const used by both.
- **`src/writers/easycrypt/render.rs`**, behaviour-preserving (all goldens unchanged). The
  one-line pieces `render_proc_open`, `render_local_decl`, `render_return`, `render_if_open`,
  `render_else_open` and `render_block_close` are now `pub`. `render_proc` and `render_stmt`'s
  `If` arm are built from them, so the listing and the files cannot drift apart.
- **`src/writers/easycrypt/mod.rs`**: `pub mod lower`, and a new
  `EcExportError::Inline(#[from] InlineError)`, transparent.
- **`src/debug/ir.rs`**, behaviour-preserving for Domino listings:
  - new `pub(crate) struct FrameScope { pkg_inst_name, frame_id }` with `key()`;
  - `rewrite_expr` and a new free `place_from_pattern` take a `FrameScope` and are `pub(crate)`,
    so both listings alpha-rename identically;
  - `InlineError` also derives `Clone, PartialEq, Eq`, which `EcExportError` needs;
  - a doc note on `frame_lines` for EasyCrypt listings.
- **`src/debug/render.rs`**:
  - new `render_side_by_side_easycrypt`;
  - `render_side_by_side` now shares `equivalence_at` and `render_listings` with it. Its output is
    byte-identical;
  - new `RenderError::EasyCrypt(EcExportError)`. An `EcExportError::Inline` is mapped back to
    `RenderError::Inline`, so `--easycrypt` reports the same errors;
  - one new test, `easycrypt_errors_are_the_domino_errors`.
- **`crates/domino`**: an `--easycrypt` flag on `Commands::Inline`, which selects the renderer.
- **Goldens**: `testdata/easycrypt/story08/inline-hello-world.txt` and
  `testdata/easycrypt/story08/inline-kem-dem-pkenc.txt`.
- **`docs/stories/easycrypt/09-debug-on-easycrypt.md`**: §2.2 gains the corrections and facts
  story 09 needs (§6).

## 2. The lowering as implemented

**Provenance.** `lower.rs` walks each frame's easycryptified *Domino* body and emits every statement
twice:

- the **EasyCrypt line**, via `package::translate_oracle_stmt` with a per-frame `FrameNaming`, then
  story 01's renderer. No EasyCrypt syntax is `format!`ted in `lower.rs`;
- the **IR node**, built from the Domino statement with `ir.rs`'s own `rewrite_expr` and
  `place_from_pattern`.

`FrameNaming` spells names as follows:

- state, and a parameter that is a module variable, becomes `EcExpr::Qualified` with the path
  `[Pkg_Inst_<inst>, var]`. As an assignment target it is the rendered path;
- locals get a listing-unique name. The first frame to use a spelling keeps it. A later frame's
  clashing local becomes `<name>_<frame id>`. Names are claimed when a frame is created (arguments,
  then every assigned local), so a caller's names are always settled first and only callees are
  ever renamed.

**Elimination rules** (all in `shape()` and `lower_block`):

| EasyCrypt (from `easycryptify`) | IR |
|---|---|
| `ec_result <- None;`, `ec_done <- false;` | nothing (unlabelled line) |
| `ec_result <- Some e;` in the entry frame | `Return { value: e }`, or `None` for `Some tt` (a valueless return) |
| `ec_result <- Some e;` in an inlined callee | `Return { value: Some e }`: the caller's `ec_r<N> : T option` receives exactly that |
| `ec_done <- true;` right after a `Return` | nothing: the block already ended |
| any other `ec_done <- true;` | `Abort`, which is exactly where the Domino oracle aborted |
| `if (!ec_done) { B }` | structural: `B`'s IR is spliced into the enclosing block and both lines are unlabelled. It is sound because every `ec_done`-setting point is already a terminal, so the guard always holds on paths that reach it |
| `x <- oget e;` (any `Unwrap`) | `Assign`; the executor lowers `Unwrap` to `maybe-get` |
| `if (!(e = None)) {…} else {…}` guard | `Branch` (`is_assert: false`; EasyCrypt has no `assert`) |
| `ec_rN <@ O.p(args);` | `Call`. The bind is `Place::Local` `ec_rN`, and `FrameInfo::return_type` is the wrapped `Maybe(T)` |
| callee falls off its end | `Abort`, on the `ec_rN <- ec_result_k;` line that also closes the frame |
| router `if (!abort_flag) {`, call comment, `if (ec_result = None) {` | structural, unlabelled |
| router `Game_X.abort_flag <- true;` | `Abort`: the entry procedure fell through, so `ec_result` is `None` |

`ec_result`, `ec_done` and `abort_flag` never become places.
`plumbing_variables_never_reach_the_ir` checks this.

**Layout.** The listing is one complete EasyCrypt procedure:

1. a header comment;
2. the router's `proc` line;
3. one `var` line per local of every frame. The entry `ec_result` carries the router's `<- None`,
   because the router's and the entry procedure's `ec_result` are merged: the router copies the
   result unchanged, so the merge is exact. The entry procedure's own arguments are the proc's
   parameters and get no `var` line;
4. the router's guard and call comment;
5. the entry body;
6. the router tail.

An inlined call looks like this:

```
(* ec_r1 <@ Pkg_Inst_Scheme_PKE.d_ENC(oget Pkg_Inst_MON_CCA_PKE.pk, m1); *)   <- Call label = frame_lines.0
  pk <- oget Pkg_Inst_MON_CCA_PKE.pk;                                          <- arg_lines
  m <- m1;
  …callee body, one level deeper…
ec_r1 <- ec_result_1;                                                          <- frame_lines.1, callee fall-through Abort
```

The `var` block has to come first, but its contents are only known after inlining. So
`inline_oracle_ec` runs the deterministic lowering twice: pass 1 collects the declarations, and
pass 2 lays them out.

**`then_lines`/`else_lines`/`arg_lines`** follow `ir.rs` exactly. `then_lines` runs from `label+1` to
the `}` or `} else {` row. `else_lines` runs from the row after that to its `}`. **`sites`** is 1:1
with labelled statements, and each `SiteInfo::line` is the trimmed row.

## 3. Judgement calls

### 3.1 `x <- oget e` is an `Assign`, not an `Unwrap`

The brief pointed out that `ir.rs` would make a whole-right-hand-side `x <- Unwrap(e)` an
`InlStmt::Unwrap` fork with an infeasible `unwrap-none` child. The lowering makes it an `Assign`
instead, for three reasons:

- in the EasyCrypt listing the line is `x <- oget e;`, and EasyCrypt's `oget` is total, with no
  failure branch;
- the abort decision already exists as the enclosing `if (!(e = None))` `Branch`;
- an `Unwrap` would add one structurally infeasible terminal, and a decision that does not exist
  in the code, per unwrap.

The executor handles it: `expr_expr.rs` lowers `Unwrap` to `maybe-get` (story 17).
`executor_walks_every_structural_path` runs every path of all four cases.

### 3.2 The router's call is not a frame

The entry frame, frame 0, is the entry *package* procedure, as in `inline_oracle`. So:

- `InlinedOracle::{args, return_type, entry_pkg_inst}` equal the Domino listing's (asserted);
- `return_type` is the Domino `T`, not the exported `T option`;
- entry-frame `Return` values are the Domino ones.

The alternative would make the router a frame, the package call a `Call`, and the router's
`return ec_result` the entry `Return`. That would give every entry return an `Unwrap(ec_result)`
value, which breaks provenance.

### 3.3 The listing is a whole procedure

Emitting the `var` block makes the listing self-contained EasyCrypt, which is what makes the compile
check honest. It costs `var` rows at the top: 2 and 5 for hello-world (small, medium), 42 and 36 for kem-dem `PKENC` (MON, MOD). A reader also sees
which callee locals were renamed, and to what.

## 4. Measurements: structural paths (`count_terminals`)

| oracle | game instance | EasyCrypt listing | Domino listing |
|---|---|---|---|
| kem-dem `PKENC` | `Game_MON_CCA_PKE` | **12** | 6 |
| kem-dem `PKENC` | `Game_MOD_CCA_PKE_Real_KEM` | **31** | 16 |
| hello-world `UsefulOracle` | `medium_composition` | 2 | 1 |
| hello-world `UsefulOracle` | `small_composition` | 1 | 1 |

Pinned by `kem_dem_pkenc_path_counts`. **The surplus is infeasible by construction.** An inlined
call that can return is followed by the caller's `if (!(ec_rN = None))`. The else side of that
guard is an explicit `ec_done <- true`, or a fall-through to the router's abort. It is reachable
only if the callee returned `None` without aborting, and the inlined callee rules that out: every
`None` it could return aborts inside it first.

Listing lengths are 142 and 151 rows for kem-dem `PKENC` (MON/MOD), against 54 and 66 Domino rows; 42 and 36 of those are the `var` block.
Most of the difference is the `var` block and the `ec_*` plumbing rows.

## 5. Tests (`src/writers/easycrypt/lower/tests.rs`)

| §4 criterion | test |
|---|---|
| prints EasyCrypt for both sides of both projects; goldens | `golden_hello_world_useful_oracle`, `golden_kem_dem_pkenc` |
| plain `domino inline` byte-unchanged | the existing `snapshot_hello_world_useful_oracle` (`testdata/story03/inline-hello-world.txt`), plus a manual `cmp` of the binary's output against a pre-change capture for hello-world and kem-dem, with and without `--no-line-numbers`: **all identical** |
| listing compiles in a minimal wrapper | `listing_compiles_as_an_easycrypt_procedure` (see below) |
| provenance for kem-dem `PKENC` | `kem_dem_pkenc_state_places_and_return_values_are_domino` |
| abort through the router's `ec_result = None` branch is `Abort`; no flag assignment in the IR | `falling_through_the_entry_procedure_aborts_at_the_router_flag`, `plumbing_variables_never_reach_the_ir`, `every_ec_done_true_that_is_not_after_a_return_is_an_abort`, and `executor_walks_every_structural_path` (the router abort is a reached terminal for `medium_composition` and MOD) |
| line ranges populated; `sites` 1:1 | `block_and_frame_line_ranges_are_populated`, `labels_are_distinct_lines_and_sites_are_1to1` |
| deterministic | `listing_is_deterministic` |

More detail on the less obvious tests:

- **`listing_compiles_as_an_easycrypt_procedure`.** It writes `Types.ec`, `Interfaces.ec` and every
  `Pkg_*`/`Comp_*` of the theorem to a temp dir, then compiles
  `require import … Comp_<X>. module Inlined = { <listing> }.` for all four listings.
  - Checked by hand: it really runs EasyCrypt (`.eco` files are produced), and a planted error
    (`Some` → `Somme`) fails it.
  - The only EasyCrypt output is the known flag-join warning `may use uninitialized local
    variables … [c_dem, c_kem]`. The exported `Pkg_MON_CCA_PKE` emits the same warning
    (story 16 §6).
- **`kem_dem_pkenc_state_places_and_return_values_are_domino`.** Every `Place::State`'s
  `(pkg_inst, field)` exists in the `DebugTransform` game. The entry-frame `Return` values equal
  the Domino IR's, in order, as `Expression`s. So do `args`, `return_type` and `entry_pkg_inst`.
- **`no_path_reads_an_unbound_local_and_the_domino_game_instance_pairs_with_it`.** It runs the
  EasyCrypt IR against the *Domino* game instance and sample info, which is story 09's pairing (§6).
  No path's SMT mentions an unbound frame key.
- **`easycrypt_errors_are_the_domino_errors`** is in `src/debug/render.rs`.

## 6. State handed to the next story

- **Signature:** `pub fn inline_oracle_ec(game_inst: &GameInstance, oracle_name: &str) ->
  Result<InlinedOracle, EcExportError>`, in `src/writers/easycrypt/lower.rs`. `game_inst` comes
  from `EasyCryptTransform`. The CLI path is `render_side_by_side_easycrypt` in
  `src/debug/render.rs`, and `domino inline --easycrypt` selects it in `crates/domino/src/main.rs`.
- **How provenance is carried:** the lowering walks the easycryptified Domino code and asks the
  writer to translate each statement (§2). There is no side table, and no EasyCrypt is parsed or
  translated back.
- **Pair the EasyCrypt IR with the Domino (`DebugTransform`) game instance** when executing. It
  runs there: state places, sample ids and entry returns are Domino's (story 16 asserts that
  `samplify`'s positions are identical in both pipelines). Do not pair it with the easycryptified
  instance, whose signatures are `Maybe(T)`.
- **Story 16 §8's hazard does not arise here.** That hazard is infeasible paths reading unassigned
  locals, which the executor writes out as illegal `<pkg#N::x>` symbols. In this IR every
  `ec_done`-setting point is a terminal, so no path reaches an `if (!ec_done)` body unassigned.
  It is tested.
- **Path counts** are in §4. Story 09 should expect the EasyCrypt run to explore more paths
  structurally, with the surplus pruned as infeasible. A *feasible* extra path is a lowering bug.
- **Painting:** only labelled lines are painted. The unlabelled rows are the `var` block, the
  `ec_*` plumbing, the `if (!ec_done) {` and `}` lines, the router's guard and call comment, and
  `return ec_result;`. They are never painted.
- **Golden paths:** `testdata/easycrypt/story08/inline-hello-world.txt` and
  `testdata/easycrypt/story08/inline-kem-dem-pkenc.txt`. Regenerate each by running
  `domino inline --easycrypt …` in the project directory and redirecting its output. No other
  golden changed.
- These facts are also written into `09-debug-on-easycrypt.md` §2.2, along with the correction
  that its `treeify` wording is stale.

## 7. Notes for follow-up

- **`--features cvc5-lib` does not build here.** The cause is `cmake: command not found` in
  `cvc5-sys`'s from-source build. It was not verified for this story. The only `cvc5-lib`-gated
  code is `domino debug` and `src/util/smtsolver`'s in-process solver, and neither uses anything
  changed here.
- **The infeasible guard-else children (§4)** could be removed structurally. The lowering would
  have to recognise `ec_rN <@ …; if (!(ec_rN = None)) { … } else { … }` and treat the else side as
  dead. That is pattern-matching `easycryptify`'s shape, and it would make the IR disagree with the
  listing. It was left for story 09 to judge with the solver's pruning in place.
- **The assert-then-unwrap duplicate guard** (story 17 §7) is visible in the listing, e.g.
  `if (!(Pkg_Inst_Key.k = None)) { if (!(Pkg_Inst_Key.k = None)) {` in `Key.GET`. The lowering
  shows the code as exported, as it should.
- **Renamed callee locals** read as `c__1` (from `c_`) or `ec_r1_1`. The `<name>_<frame id>`
  scheme ties a name to the frame id in the IR keys. EasyCrypt's own `inline` tactic uses a
  different scheme, so the names will not match a proof goal's. Matching them is a
  tactic-generation-epic concern.
- **Formatting:** only the two new files (`lower.rs`, `lower/tests.rs`) were run through
  `rustfmt`. The touched existing files follow story 16 §10.
- `docs/easycrypt-interaction-and-branching.md` shows as modified in `git status`. That edit is the
  owner's own, in progress, and unrelated to this story; this session did not touch it.
