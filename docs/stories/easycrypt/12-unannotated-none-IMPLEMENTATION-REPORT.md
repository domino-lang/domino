# Story 12 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (342 passed, 4 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`~/.opam/easycrypt/bin/easycrypt`, resolved via the developer's opam switch) was on
`PATH`, so every compile-shaped test ran for real, plus the story's own §5 recipe was run by hand
for `Simple4WHS`, `Full4WHS` and `kem-dem-cca-ssp`.

## 1. What changed

### 1.1 The rendering change (§3.1)

- `src/writers/easycrypt/render.rs:528`: `EcExpr::None_(ty) => format!("None<:{}>", render_type(ty))`
  became `EcExpr::None_(_) => "None".to_string()`. The single rendering site, unconditional, exactly
  as the story specified.
- `src/writers/easycrypt/ast.rs:161-169`: the `None_(EcType)` doc comment now says the opposite of
  what it said before this story — bare `None` renders in every position the exporter emits, never
  `None<:t>` — and explains *why* the `EcType` is kept anyway even though nothing reads it today:
  story 08's lowering to the debugger IR (`src/debug/ir.rs`) will need the type of an abort value,
  and dropping the field now would mean re-adding it later. **`EcExpr::None_` still carries its
  `EcType`** — the field itself is untouched, only the render arm and the doc comment changed.

### 1.2 No fallback (§3.2)

`render_expr_inner`'s `None_` arm takes no heuristic branch and never inspects the type — confirmed
by `grep -n "None_" src/writers/easycrypt/render.rs` showing exactly the one match, `_` on the type.
`Some`, `oget`, and empty-`fmap` (`MapEmpty`) rendering are untouched (§6) — no other arm in
`render_expr_inner` was edited.

### 1.3 A real "future construct" — found, not invented (§3.2's own prediction)

The story's own risk section says: *"if a future construct ever needs an annotation, `easycrypt
compile` fails loudly on that golden and the fix is targeted at that construct."* That happened for
real, on `Full4WHS` (which story 12's own §5 recipe doesn't drive end to end, but the epic's testing
ladder and this session's brief both required compiling): `Full4WHS`'s
`Eq_H6_1_1_H7_0_Invariants.ec` failed `easycrypt compile` with
`this operator type contains free type variables` on `Domino_freshness_and_honesty_matches` — the
exact failure mode the story's `op bad = None.` example predicts.

Root cause: `example-projects/4WHS/theorem/full/invariant-H6_1-H7_0.smt2`'s hand-written
`freshness-and-honesty-matches` binds `(let ((none (as mk-none (Maybe ...)))) (forall ... (=> (not
(is-mk-none state)) ...)))` — the body calls `is-mk-none` directly instead of comparing against the
bound `none`, so `none` is dead. Before this story, `none`'s `(as mk-none (Maybe T))` sort annotation
made `let none = None<:T> in <body not using none>` monomorphic regardless of use; after this
story's change it is `let none = None in <body not using none>`, and an unused `let`-bound bare
`None` leaves its type a genuinely free type variable, which is a hard `op`-level error in EasyCrypt
even though the binding is never read.

**Fix, scoped narrowly to that construct** (`src/writers/easycrypt/invariant.rs::translate_let`):
elide a `let` binding when its *value is exactly `EcExpr::None_`* and the (already-translated) body
never references the mangled name — added a small recursive `expr_references_var` helper (covers
every `EcExpr` variant, conservative around shadowing, which this translator's `Names` mangling
never actually produces). This is deliberately **not** general dead-`let` elimination: an unused
binding to a *concretely-typed* value (e.g. `Domino_state_eq` in
`testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` binds `k = (oget state).\`6` and
never uses it) is left exactly as it always rendered — that dead code was already harmless to
`easycrypt compile` (the value is monomorphic) and is not this story's concern; the first version of
this fix used a fully general elision and it changed that golden's byte content (dropped `k`'s
binding entirely), which the story's own review rule ("if a golden line changes in another way,
that's a bug") caught. The final, `None_`-only version leaves every other golden untouched.

Swept the rest of `example-projects/4WHS/theorem/full/*.smt2` (14 occurrences of `let ((none ...`
across 3 files) and `example-projects/4WHS/theorem/simple`, `kem-dem-cca-ssp`'s invariant files for
the same shape (an unused `let`-bound `none`/`mk-none`): this is the *only* occurrence in the whole
test-bed. Confirmed by re-running every `*_full_tree_compiles_in_dependency_order` test (all green)
and by hand-compiling every `Eq_*_Invariants.ec` and `Eq_*.ec` file of `Simple4WHS`, `Full4WHS` and
`kem_dem_cca_ssp` with `easycrypt compile -I .` (§3 below).

### 1.4 Test-expectation updates

Two pre-existing unit tests in `invariant.rs` hardcoded the old `None<:...>` string and needed their
expected values updated (not new tests — the rendering change was always going to require this):
`is_mk_none_and_maybe_get_translate` and `mk_some_and_as_mk_none_translate`.

### 1.5 Goldens (§3.3)

Regenerated mechanically: every `.ec` file under `testdata/easycrypt/` containing `None<:` (30
files, across `story01`, `story03`, `story04`, `story06`) had `None<:[^>]*>` replaced with `None` —
safe because `render_type` never itself emits `<` or `>` (confirmed by inspection: `Int`/`Bool`/
`Unit`/`Named`/`Tuple`/`Option`/`Fmap`/`Distr`/`Fun` all render without angle brackets), so the first
`>` after `None<:` is always the matching close. Verified programmatically that every changed line
in every file reduces to *only* that substitution (`git diff` per file, each `-`/`+` line pair
checked by re-applying the regex to the old line and asserting it equals the new line) — the golden
diff is `30 files changed, 547 insertions(+), 547 deletions(-)`, none of it beyond the `None`
spelling. `.eco` files are gitignored build artifacts (confirmed via `git ls-files`/`.gitignore:8`),
not tracked goldens — nothing to hand-regenerate or commit there; they get rebuilt fresh by
`easycrypt compile` (content hash changed, so stale `.eco`s are never reused).

## 2. Acceptance criteria, checked against what was actually built

- [x] `grep -rn "None<:" _build/easycrypt/ testdata/easycrypt/` — repo root has no top-level
      `_build/easycrypt`; export writes under `<project>/_build/easycrypt/<theorem>/`. Ran
      `grep -rn "None<:" example-projects/4WHS/_build/ example-projects/kem-dem/kem-dem-cca-ssp/_build/
      testdata/easycrypt/` after exporting Simple4WHS, Full4WHS and kem_dem_cca_ssp fresh: no hits
      (exit 1).
- [x] Every exported file of 4WHS `Simple4WHS`, `hello-world`, `simple-KEM-example` and
      `kem-dem-cca-ssp` still compiles with `easycrypt compile -I .` — `hello-world` and
      `simple-KEM-example` still fail *before* any file is written, with the exact pre-existing
      invariant-dialect gap from story 07 §6.2 / story 10 §3 (`unsupported SMT sort
      <GameState_MediumComposition_...>` / `<GameState_Prot>`), unrelated to and unaffected by this
      story — reproduced by hand, identical to stories 10/11's reports. `Simple4WHS` and
      `kem-dem-cca-ssp` compile every file end to end except the pre-existing story 07 §6.1
      base-case `smt(emptyE map_empty)` gap on their `Eq_*.ec` files (same `[critical] ... cannot
      prove goal (strict)` at line 18, present before this story too). `Full4WHS` (50 files, not
      itself named in story 12 §4 but required by this session's brief) compiles identically —
      every `Types.ec`/`Interfaces.ec`/`Variant_*.ec`/`Comp_*.ec`/`Eq_*_Invariants.ec` clean,
      including the one file this story's change actually broke and then fixed
      (`Eq_H6_1_1_H7_0_Invariants.ec`, §1.3), and every `Eq_*.ec` hits only the same known base-case
      gap.
- [x] `EcExpr::None_` still carries its `EcType`, and `ast.rs`'s comment explains why — §1.1.
- [x] The golden diff contains no change other than the `None` spelling — §1.5, verified
      programmatically, not just eyeballed.
- [x] Deterministic; `cargo build/test/clippy --workspace` clean.

## 3. Verification run by hand, end to end

```
cargo build --workspace
D=$PWD/target/debug/domino
```

- **hello-world** / **simple-KEM-example**: export fails pre-file-write with the pre-existing gap,
  unchanged from stories 10/11 — verified via the fallback (targeted unit tests already exercising
  `None` rendering, e.g. `is_mk_none_and_maybe_get_translate`), matching this session's brief's own
  fallback instruction.
- **Simple4WHS**: `wrote _build/easycrypt/Simple4WHS (19 files)`. `grep -rn "None<:" .` → no hits.
  Compiled `Types.ec Interfaces.ec Variant_*.ec Comp_*.ec Eq_*_Invariants.ec` clean; every `Eq_*.ec`
  hits only the known base-case gap.
- **Full4WHS**: `wrote _build/easycrypt/Full4WHS (50 files)`. Before the `translate_let` fix,
  `Eq_H6_1_1_H7_0_Invariants.ec` failed with `this operator type contains free type variables`
  (§1.3); after the fix, every non-`Eq_*.ec` file compiles clean and every `Eq_*.ec` hits only the
  known base-case gap, same as Simple4WHS.
- **kem-dem-cca-ssp**: `wrote _build/easycrypt/kem_dem_cca_ssp (17 files)`. Same pattern: everything
  clean except the one known base-case gap on `Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.ec`.
- `cargo test --workspace`: 342 passed, 0 failed, 4 pre-existing `#[ignore]`d — includes the three
  `*_full_tree_compiles_in_dependency_order` tests (Simple4WHS, Full4WHS, kem-dem-cca-ssp), all
  green with this story's changes in place, i.e. this isn't only a by-hand check.
- `cargo clippy --workspace --all-targets`: clean.

## 4. State handed to the next story

- **`EcExpr::None_(EcType)` is unchanged as a type** — only its render arm and doc comment moved.
  Story 08's lowering to `src/debug/ir.rs` can read the carried `EcType` exactly as before; nothing
  about this story removes or renames the field.
- **`translate_let` (`invariant.rs`) now elides a `let` binding when, and only when, its value is
  `EcExpr::None_` and the body never references it.** This is deliberately not general dead-code
  elimination — every other unused `let` binding the translator emits (bound to a concretely-typed
  value) is left in place, unchanged from before this story, so no other golden's content moved. If
  a later story needs to elide other dead bindings too, `expr_references_var` (new, free function in
  `invariant.rs`, covers every `EcExpr` variant) is already there to build on — but widening the
  `is_dead_none` condition to "any unused binding" would very likely touch
  `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` again (it has at least one:
  `Domino_state_eq`'s unused `k`), so do that as its own reviewed change, not silently.
- **The one occurrence of an unused `let`-bound `none`/`mk-none` in the whole test bed** is
  `example-projects/4WHS/theorem/full/invariant-H6_1-H7_0.smt2`'s `freshness-and-honesty-matches`
  (hand-written SMT-LIB, pre-existing, not touched by this story). It is not itself a bug worth
  fixing at the source level — the translator now handles it correctly — but if a future story
  audits `.smt2` invariant sources for dead `let`s, this is the one instance on record.
- **`Full4WHS` is now a real regression check for this exact failure class** — it's the only project
  in the test bed that exercised the "unused bound `None`" shape, and it's covered by
  `full_4whs_full_tree_compiles_in_dependency_order`, which shells out to real `easycrypt compile`
  on every generated file. A later story touching `translate_let` or `None_` rendering again should
  keep running that test, not just the golden-file tests, since this exact bug was invisible to the
  golden-file comparisons (Full4WHS's invariant files aren't golden-tested, only compile-tested).

## 5. Notes for follow-up (not this story's scope)

- `cargo fmt --check` is not clean across this repository (pre-existing, unrelated to this story —
  reproduced on files this story never touched, e.g. `src/debug/driver.rs`, and on parts of
  `src/writers/easycrypt/ast.rs`/`package.rs`/`proof.rs`/etc. that predate this story). The installed
  `rustfmt` (1.9.0-stable) appears to disagree with whatever formatting convention/version produced
  the existing code (e.g. it wants every struct-like enum variant broken onto multiple lines; the
  codebase consistently keeps short ones on one line). Not touched here — out of scope, and the
  epic's own testing ladder (00-overview.md §7) does not include `cargo fmt --check`.
- The pre-existing base-case `smt(emptyE map_empty)` gap (story 07 §6.1) and the hello-world/
  simple-KEM-example invariant-dialect gap (story 07 §6.2) are both exactly as documented before
  this story, reproduced identically during verification, and untouched by this story's changes.
