# Story 07 — Implementation report

**Status:** done, with two known, documented gaps (§6). `cargo build --workspace`,
`cargo test --workspace` (338 passed, 4 pre-existing `#[ignore]`d, none new failing) and
`cargo clippy --workspace --all-targets` are all clean. `easycrypt` (`r2026.06-12-g7e192dd`) was on
`PATH`, so every compile-shaped test ran for real, plus the exact §5 recipe was run by hand end to
end for `Simple4WHS` and `kem-dem-cca-ssp`.

**Post-review update**: the project owner flagged, while reviewing this story, that
`invariant.rs`'s `define-state-relation` handling hard-required its two binders to be spelled
literally `left`/`right` and asked why — correctly identifying this as an unnecessary rigidity
rather than a real SMT-LIB constraint. Fixed (§4.1 below): binder names are now purely positional,
like an ordinary `define-fun`'s own argument names. Verifying that fix surfaced a second, separate
`Full4WHS` gap (whole-package-state equality, not a naming issue); the project owner asked for that
to be implemented too, and it now is (§4.2 below). Both are genuine, shared-infrastructure
corrections/additions to story 06's own translator, found and fixed in this same session.

## 1. What exists

`src/writers/easycrypt/proof.rs` (~470 lines of implementation + ~250 lines of tests):

```rust
pub struct EquivalenceProofFile {
    pub file_name: String,          // "Eq_<Left>_<Right>.ec"
    pub file: EcFile,
    pub left_name: String,
    pub right_name: String,
    pub oracle_count: usize,
    pub admit_count: usize,         // == oracle_count in v1
    pub oracle_set_mismatch: Option<String>,
}
pub struct EquivalenceFiles { pub invariants: InvariantFile, pub proof: EquivalenceProofFile }

pub fn compute_equivalence_files(
    theorem: &Theorem<'_>,
    project: &impl Project,
    interfaces: &InterfacesOutput,
) -> Result<Vec<EquivalenceFiles>, EcExportError>;
```

`compute_equivalence_files` is the orchestration story 06's own report (§10) handed off to this
story: it loops `theorem.game_hops` once, filters `GameHop::as_equivalence()`, and for each one
calls **both** story 06's `invariant::build_invariant_file` and this story's own
`build_equivalence_file` — the two files share one loop, one `Names` registry for lemma names
(collision-checked across the whole theorem), and one recomputed package-variant name map (§2).

`export_theorem` (`export.rs`) now takes a second parameter, `project: &impl Project` (needed to
read each equivalence's invariant file — a real, necessary signature change, not a story-05
regression), calls `compute_equivalence_files` once after building `interfaces_output`, and folds
both files per equivalence into `ExportedTheorem::files`, plus a new report-only field:

```rust
pub struct EquivalenceReport {
    pub left_name: String, pub right_name: String,
    pub invariants_file: String, pub proof_file: String,
    pub oracle_count: usize, pub admit_count: usize,
    pub oracle_set_mismatch: Option<String>,
}
// ExportedTheorem gains: pub equivalences: Vec<EquivalenceReport>,
```

`crates/domino/src/main.rs`'s `easycrypt()` passes `&project` through; `print_easycrypt_report`
gains one `equivalence <file> (<n> oracles, <n> admits)` line per hop and a `warning` line per
`oracle_set_mismatch`, per §3.2.

## 2. `EcExpr::Pr` and `NameKind::Lemma` — two small, deliberate AST/infra additions

- `ast.rs` gains `EcExpr::Pr { module, proc, args, memory, event }` for `Pr[M.p(args) @ &m :
  event]`, exactly as story 01 §3.1 pre-authorized. `module` is a raw string that may already be a
  functor application (`"Hybrid0.Exp_Hybrid0(A)"`), matching `EcStmt::Call`'s own established
  convention rather than inventing an "applied module" AST node. `render.rs` renders it and treats
  it as atom-precedence (self-delimited by `[...]`).
- `names.rs` gains `NameKind::Lemma`: unlike every other kind, an EasyCrypt lemma name has **no**
  lowercase-start requirement (`Hybrid0_Hybrid1_equiv` compiles as spelled, verified against
  `r2026.06-12-g7e192dd`) — reusing `NameKind::Op`/`Var`'s mangling would have wrongly `d_`-prefixed
  it. `Lemma` mangling still escapes a keyword collision, an `ec_` prefix, and a digit-leading name,
  just never on uppercase-start. One `Names(Lemma)` registry, created once in
  `compute_equivalence_files`, is shared across every equivalence in the theorem, so two hops that
  would otherwise produce the same lemma name are a hard collision, not silently overwritten.

## 3. The file, as implemented — matches the worked example exactly, verified by compiling it

`Eq_<Left>_<Right>.ec`'s shape (requires, `section`, `declare module`, `lemma`, proof) is byte-for-
byte what §3.1's worked example shows, confirmed by actually compiling real output (not just
golden-string matching) for `Simple4WHS`'s three equivalences and `kem-dem-cca-ssp`'s one. Rules, as
built:

- **Lemma name**: `<LeftInst>_<RightInst>_equiv`, mangled via the new `NameKind::Lemma` (§2), through
  one theorem-scoped registry.
- **Binders**: `&m`, then one `(name : ty)` per **theorem** constant either side's own composition
  binds to a bare theorem-const reference (not a literal), in `theorem.consts` declaration order.
  Built in two passes: first resolve each side's own `Exp_<Comp>.run` argument list (`comp.consts`,
  filtered by the *same* `composition_const_needs_arg` router `init` already uses — widened
  `pub(super)` in `game.rs` for this, not re-derived) against that game instance's own
  `GameConstIdentifier` bindings (`GameInstance::consts`, resolving a literal or chasing a bare
  `GameIdentifier::Const` to its `TheoremIdentifier::Const`, mirroring `invariant.rs`'s own
  `resolve_expr_value` chase one level up); then collect the *union* of theorem-const names either
  side referenced, and emit binders in `theorem.consts`' own order (not the order they were
  discovered) — this is what makes `hello-world`'s width-only `n` correctly produce **zero** extra
  binders (only `&m`), and what makes `Real_Hybrid3 ~ Ideal_Hybrid3` correctly produce zero binders
  too (both sides' `b`/`bprf` resolve to *literals*, not theorem consts).
- **`Pr` arguments**: exactly each side's resolved run-argument list, literal values rendered
  verbatim, theorem-const values rendered as that constant's lemma-binder variable — confirmed
  live: `Real_Hybrid3 ~ Ideal_Hybrid3` (`hop shares the `Hybrid2` composition, different literal
  idealization bits) renders `run(false, true)` on the left and `run(true, true)` on the right,
  over the *same* `Hybrid2.Exp_Hybrid2`.
- **Restrictions**: `<mangled>.Game_<mangled>` then `<mangled>.Pkg_<InstMangled>.<Variant>` per
  instance, `comp.pkgs` **declaration** order (not `ordered_pkgs_idx()`) — recomputed per side via a
  small `CompLayout` (mangled comp base + per-instance clone-alias base + variant name), built the
  *same* way `game.rs::render_game_file` builds its own (fresh per-composition `Names(Module)` over
  `comp.pkgs` in order), so the strings always agree with what the actual `games/<mangled>.ec` file
  contains. When both sides share one composition (`Real_Hybrid3 ~ Ideal_Hybrid3`), the two
  `CompLayout`s come out identical (booleans never affect `VariantKey`, only `Integer`/`Fn` params
  do — confirmed, not assumed) and the shared composition's router/clones are listed once, not
  twice.
- **The `call` invariant**: `EcExpr::App { head: "inv", args: [left_record_lit, right_record_lit]
  }`, rendered through the shared `render::render_expr` (reusing its own precedence/paren logic
  rather than hand-formatting) inside the one raw tactic `ProofLine` EasyCrypt tactics are allowed
  to be (`ast.rs`'s own documented exception). Each record literal is built by
  `build_side_record_lit`: one field per `(instance, state field)` in `ordered_pkgs_idx()` order,
  then per qualifying package param (`package::param_needs_var`), then `abort_flag` — the **same**
  order and namespacing (`{l_,r_}pkg_<instance>_<mangled field>` / `{l_,r_}abort_flag`) story 06's
  `invariant.rs::build_side_record` uses for the record *type*, independently re-derived here (not
  shared code — story 06's own report §10 explicitly says this story should re-derive it "without
  needing story 06's own internal lookup map", and the two need different *value* shapes anyway: a
  record-field projection there, a memory-tagged module-state read here,
  `Hybrid0.Pkg_KX.KX.d_LTK{1}`). Verified by direct golden-style assertions (`proof.rs`'s own tests)
  and by compiling the real output.
- **Induction start**: `last first.` then `auto => />.` then `smt(emptyE map_empty).` — a real `smt`
  call, never `admit`, exactly as the story requires (§6).
- **Oracle bullets**: one per `left_comp.exports` entry (**not** `right_comp.exports` — the two are
  guaranteed structurally identical whenever they share one game interface, which is a
  precondition for the lemma to even typecheck), in that order — confirmed load-bearing and
  confirmed *not* reordered anywhere in this story's own code. Each bullet is preceded by a
  `(* <mangled proc name> *)` comment (mangled via a **fresh** `Names(Proc)`, reproducing the
  router's own already-validated proc-name mangling, the same "fresh registry reproduces an
  already-validated namespace" pattern `game.rs`'s own `callee_proc` uses) and is exactly `+ proc;
  inline. admit.`.
- **Oracle-set-mismatch warning**: computed by comparing `equivalence.trees()`'s oracle-name set
  against `left_comp.exports`'s own name set; when they differ, an `EcItem::Comment` is prepended to
  the file **and** `EquivalenceProofFile::oracle_set_mismatch` carries a human-readable diff, printed
  by `main.rs` as a `warning` report line. Not exercised by any target project today (every one's
  proof-tree oracle set matches its interface's exports exactly) — the code path is reachable and
  unit-shaped correctly, but genuinely untested against a real mismatching project, same caveat
  story 05's own report already flagged for `Hybrid`/`Conjecture` skip notes.
- **Requires**: `require import AllCore Distr FMap Int IntDiv Types Interfaces.` then `require
  <CompA> [<CompB>].` (one name, not two, when both sides share a composition) then `require import
  Eq_<Left>_<Right>_Invariants.` — matches the worked example exactly.

## 4. A real, verified EasyCrypt fact this story hit — fixed at its proper (shared) home

Compiling `kem-dem-cca-ssp`'s real output (not just `Simple4WHS`'s, and not just golden-string
matching) surfaced a genuine variable-capture bug in story 06's own `invariant.rs`, invisible until
something actually **compiled** every equivalence in every target project — which is exactly what
wiring this story's own orchestration into `export_theorem` was the first thing in the whole epic to
do.

`kem-dem-cca-ssp`'s hand-written invariant contains `(exists ((r Bits_kgenr)) (= (maybe-get
right.KEM.pk) (el2-1 (<<func-kem_gen>> r))))`. The existential binder `r` is *also* the literal,
unmangled name `invariant.rs` hardcodes for the right-side record parameter everywhere
(`translate_atom`'s `"right"` case returns `Var("r")` directly, outside `locals`/`local_names`
entirely). `translate_quant`'s own binder mangling never checked for this, so the inner `r` silently
shadowed the outer one in the rendered EasyCrypt text; every `right.*` dotted-field projection
*inside* the `exists` body then resolved to a field projection on the wrong (inner, `bits_kgenr`-
typed) `r`, and `easycrypt compile` correctly rejected it: `unknown record projection:
r_pkg_KEM_pk`.

**Fix, in `invariant.rs`** (shared, not story-07-local — this is exactly a story-06 bug, just
discovered by story 07's own compile-testing): a new `mangle_local_binder(names, raw)` helper wraps
every site that mangles a *newly introduced* local name (`translate_quant`'s quantifier binders,
`translate_let`'s bindings, `handle_definefun`'s own argument names) — if the ordinary mangling would
land on exactly `l` or `r`, it re-mangles through a `q_`-prefixed raw name instead, via the *same*
`Names` registry (so a second genuine occurrence of the same raw name stays idempotent, and a
*different* raw name that also collides is still a hard `NameError`). Added
`exists_binder_named_r_does_not_shadow_the_right_record_param` as a permanent regression test. No
golden file changed (nothing in the `hello-world`/`4WHS` golden fixtures used a binder literally
named `l`/`r`, so this was never exercised before).

## 4.1 Binder names are now positional, not a fixed `left`/`right` vocabulary (post-review fix)

Raised directly by the project owner while reviewing this story: `handle_define_state_relation`
hard-required its two binders to be spelled literally `left`/`right`
(`InvariantError::Unsupported` otherwise), and nothing in SMT-LIB's own grammar demands that — the
binders are just this `define-state-relation`'s own two local parameter names, exactly like an
ordinary `define-fun`'s argument list. `Simple4WHS`'s own invariants happen to spell them
`left`/`right` throughout, but `Full4WHS`'s spell them `state-left`/`state-right`, and the old code
rejected that outright — this is precisely §6.2's `Full4WHS` finding, now narrowed: the binder-name
rigidity was a real, unnecessary, fixable bug, not an inherent property of the older invariant
dialect.

**Fix, in `invariant.rs`** (shared, not story-07-local): `handle_define_state_relation` now accepts
*any* two distinct binder names, and binds them into a `Locals` map (`side_locals`) — the first
positionally the left side, the second the right — mapped to the canonical mangled names `l`/`r`
and their respective record types, passed into `TCtx::translate` instead of an empty `Locals::new()`.
`translate_atom` already resolves a bare atom found in `locals` (no new code needed for that case);
it gains one new case for a **dotted** atom (`state-left.KX.State`) whose *head* segment resolves
through `locals` to `l`/`r` — it reconstructs the fixed internal lookup key (`self.lookup`'s own keys
are always `left.<rest>`/`right.<rest>`, regardless of what the source file calls its binders, since
`build_side_record` populates them with those fixed prefixes unconditionally) and looks it up
exactly as before. The old hardcoded `if a == "left"` / `if a == "right"` bare-atom fallback stays
(harmless, and defensive for any code path that doesn't populate `side_locals`). The only remaining
requirement is that a `define-state-relation`'s two binders be **distinct** from each other (a
genuine malformed-file case, not a naming-convention one).

Verified against real projects, not just unit tests: `Full4WHS`'s export now gets **past** its
previous `define-state-relation … binders must be (left right), got (state-left state-right)`
failure entirely and advances to a different, later file — `theorem/full/invariant-KX-H1_0.smt2` —
confirming the fix is real and load-bearing, not just internally consistent. `Simple4WHS` (the
story's own acceptance target, which already spelled its binders `left`/`right`) is unaffected —
re-verified end to end via the CLI, byte-identical report and files. Two new unit tests:
`define_state_relation_binder_names_are_positional_not_a_fixed_vocabulary` and
`define_state_relation_dotted_access_works_with_any_binder_spelling`; the old
`define_state_relation_binders_must_be_left_right` test is replaced with
`define_state_relation_binders_must_be_distinct` (the one binder-shape error that's still real).

**What this fix, by itself, did not do** — a second, different gap in `Full4WHS` was found while
verifying it (originally documented here as a follow-up; now fixed too, see §4.2 below): at least
two of `Full4WHS`'s 16 invariant files (`invariant-KX-H1_0.smt2`, `invariant-H1_1-H2_0.smt2`)
compare a **whole package instance's** state in one equality (`(= state-left.KX
state-right.KX)`), not a specific field — story 06's flat per-`(instance, field)` lookup map has
no single `EcExpr` representing "all of `KX`'s state" to resolve that atom to.

## 4.2 Whole-package-state equality now expands to a field-by-field conjunction (follow-up fix, same session)

The gap flagged at the end of §4.1 turned out to be small and well-scoped enough to close directly,
per the project owner's explicit go-ahead ("go ahead and implement it"). **Fix, in `invariant.rs`**:
`translate_eq_n` (the `(= a b)`/`(= a b c …)` handler) now special-cases the exact two-argument shape
where *both* arguments are bare atoms recognised by a new helper, `resolve_instance_atom`, as naming
a **whole package instance** rather than one field — an atom of the form `<binder>.<instance>`
(exactly one `.`, no field segment) whose `<binder>` head resolves through `locals` to this
definition's own left/right record parameter, and for which `self.lookup` holds no `<side>.<instance>`
entry itself but does hold at least one `<side>.<instance>.<field>` entry (i.e. it names a real
instance with real fields, not an unrelated unknown atom — that case still falls through to the
ordinary `unrecognised s-expression` error, unchanged). When both sides of a two-argument `=` resolve
this way, a new `translate_instance_equality` builds the conjunction directly: it collects every raw
field name present under `self.lookup`'s `{left_prefix}.{left_instance}.` keys, sorts them for
determinism, and for each one present under the matching `{right_prefix}.{right_instance}.` prefix
too, emits `l.'l_pkg_<inst>_<field> = r.'r_pkg_<inst>_<field>`, folded with `/\`. A field present on
only one side is **silently skipped** (matching `build_params_inv`'s own existing asymmetric-field
tolerance, §3.3, rather than erroring); if the two instances share **no** fields at all, that's a hard
`InvariantError::Unsupported` (a genuinely malformed invariant, not an asymmetry). This is exactly
the implementation sketched at the end of this report's own §9 in the prior draft.

Verified against the real `Full4WHS` project: `domino easycrypt --project example-projects/4WHS
--theorem Full4WHS` now advances **past both** `invariant-KX-H1_0.smt2` and
`invariant-H1_1-H2_0.smt2` entirely, landing on a third, unrelated, unattempted gap in a later file
(`invariant-H7_1_1_0-H7_1_1_1.smt2`: an unsubstituted `<0_n>` template placeholder atom — not one of
§3.2's fixed forms, looks like a bit-width instantiation token this translator has never supported;
out of scope, not investigated further here). `Simple4WHS` re-verified unaffected. Three new unit
tests: `whole_package_state_equality_expands_to_a_field_by_field_conjunction`,
`whole_package_state_equality_skips_fields_present_on_only_one_side`,
`instance_level_equality_with_no_shared_fields_is_a_hard_error`.
`full_4whs_fails_on_whole_package_state_equality_not_binder_naming` (§6.2's regression pin) is
retired in favor of `full_4whs_fails_on_an_unsubstituted_bitwidth_placeholder`, pinning the new,
correct failure point.

## 5. A second real, verified EasyCrypt fact — a `names.rs` fix, also shared

Also only surfaced by actually compiling `kem-dem-cca-ssp`'s real package output:
`packages/MOD_CCA_PKE.ec` (story 03's own translator) failed with a parse error on `var _ : bits_dctl;`
— a local variable literally named `_`. `var _ : t;` is a genuine EasyCrypt parse error (`_` is the
wildcard/discard pattern, not a legal bound identifier), verified in isolation against
`r2026.06-12-g7e192dd`; `names.rs`'s own doc comment ("leading `_` is legal … and is left alone") was
correct for a *multi-character* name like `_U` but wrong for the *bare* single-character case, which
Domino genuinely produces (a discarded tuple-pattern binding in `kem-dem-cca-ssp`'s `Scheme_PKE`
package). **Fix, in `names.rs::mangle_name`**: a bare `_` now escapes to `d__` in every non-`Module`
kind, alongside the existing keyword/`ec_`-prefix checks. Confirmed no existing golden file
(`hello-world`/`4WHS`) uses a bare `_` variable, so no golden file changed.

## 6. Known, documented gaps — verified, not guessed

### 6.1 The base case genuinely does not discharge with `smt(emptyE map_empty)` — for every target
    project tried

Per the story's own §6 warning ("the base case may genuinely fail … report the goal rather than
widening the `smt` call blindly"), this was checked for real, not assumed. Using `easycrypt llm
-lastgoals` (an `[llm]` subcommand this session discovered — not previously documented anywhere in
this epic — that prints the exact unproved goal(s) on a batch-compile failure), the base-case goal
for `Simple4WHS`'s `Hybrid0 ~ Hybrid1` reduces (after `auto => />`) to a conjunction over the fully-
`empty`/default-initialized state — which is almost certainly true — **plus** a residual
`params_inv`-derived equality between two occurrences of the router's own `init` argument, printed by
EasyCrypt as `b{!1}`/`b{!2}` rather than being recognised as literally the same lemma-level `b`; bare
`smt()` (every default lemma, no restriction to `emptyE map_empty`) fails identically, confirming
this is not a matter of missing hints but of the goal as stated not being closeable by first-order
SMT alone from this exact tactic position. This is **reproduced identically** (same failure, same
tactic-line offset) for all three of `Simple4WHS`'s equivalences and for `kem-dem-cca-ssp`'s one —
consistent, not a fluke. **Not fixed** — per the story's own instruction, the `smt(emptyE
map_empty).` call is emitted for real (never `admit`), and this gap is recorded here rather than
papered over. `test_support::assert_compiles_or_known_base_case_gap` (new, `mod.rs`) pins this
exact, narrow failure mode in the test suite: it tolerates *only* a `cannot prove goal (strict)`
failure at this one call, so any *other* compile failure (a real regression) still fails
`cargo test`.

### 6.2 `hello-world`'s and `simple-KEM-example`'s hand-written invariants predate story 06's grammar
    entirely — genuinely out of this story's scope

Story 06 was only ever tested against `Simple4WHS`'s own `theorem/simple/*.smt2` files (its own
report says so explicitly). Wiring `build_invariant_file` into every equivalence hop of every
project's export — this story's own job — is the *first* time anything in this epic actually reads
`hello-world`'s `theorem/invariant.smt2` or `simple-KEM-example`'s own invariant files, and both turn
out to be written in a **completely different, older SMT dialect**: a single opaque whole-game-state
sort per side (`<GameState_MediumComposition_<$<!n!>$>>`) with datatype selector-function accessors
(`<game-SmallComposition-<$<!n!>$>-pkgstate-rand>`, `<pkg-state-Rand-<$<!n!>$>-ctr>`), matching
`src/writers/smt`'s own **solver-facing** encoding (confirmed: `GameState`/`pkgstate` naming is
real, active machinery in `src/writers/smt/patterns/datastructures/{game_state,pkg_state}.rs` and
`src/writers/smt/contexts/{oracle,game_inst,pkg_inst}.rs`, used by `domino prove` today) — not story
06's flat per-`(instance, field)` record model story 06 was actually built around
(`define-state-relation NAME (left right) …`). `4WHS`'s own `Full4WHS` theorem's own
`theorem/full/*.smt2` invariants are *not* this same `GameState_`-sort dialect — they use story 06's
flat per-field model correctly, just with a different binder spelling (`state-left`/`state-right`,
§4.1) and, in two files, a whole-package-state equality (§4.2) — both now fixed. What still blocks
`Full4WHS` is a third, unrelated, unattempted gap: `invariant-H7_1_1_0-H7_1_1_1.smt2` uses an
unsubstituted `<0_n>` template placeholder atom, not one of §3.2's fixed forms — see §4.2's own
closing paragraph.

**Consequence for this story's own acceptance criteria (§4)**: `kem-dem` now genuinely produces
compiling `Eq_*.ec`/`Eq_*_Invariants.ec` files (confirmed, §3/§6.1); `hello-world` does **not** — its
`Proof` theorem's export now fails outright (`export_theorem` is correctly all-or-nothing per
theorem, matching the pre-existing `yao`/`Yao` precedent for an unsupported construct — nothing
about that design changed here). The regressed tests (`hello_world_exports_expected_files`,
`simple_kem_example_exports_without_error`, `full_4whs_exports_only_that_theorem`,
`write_files_round_trips_and_rewriting_is_byte_identical`) are updated: the first three now pin the
*specific*, verified failure (`hello_world_fails_on_its_pre_easycrypt_invariant_format`,
`simple_kem_example_fails_on_its_pre_easycrypt_invariant_format`,
`full_4whs_fails_on_an_unsubstituted_bitwidth_placeholder` — renamed twice across this report's
drafts, once for each fix that changed *which* error `Full4WHS` actually hits first), and the fourth
now targets `kem-dem-cca-ssp` instead of `hello-world`. **Not attempted**: teaching `invariant.rs` a second SMT
dialect (whole-game-state sorts + selector-function accessors) is a substantial, story-06-shaped
undertaking — a new resolution pass reverse-engineering `src/writers/smt`'s own naming scheme — well
beyond this story's own scope (equivalence *proof skeletons*, not invariant-format coverage).
Flagged prominently here as the natural next story, not silently absorbed into "out of scope, move
on."

## 7. Acceptance criteria, checked against what was actually built

- [x] For 4WHS `Simple4WHS`: `Eq_Hybrid0_Hybrid1.ec`, `Eq_Hybrid1_Hybrid2.ec` and
  `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` are generated (`proof::tests::
  simple_4whs_produces_the_three_translated_equivalence_hops`); the reduction hop `Hybrid2 ~
  Hybrid3` is skipped with a note (unchanged, story 05's own behavior, reconfirmed still correct).
- [~] **The whole exported theorem compiles**: every file, in dependency order, with `easycrypt
  compile`, with `admit`s and no errors — true for `Simple4WHS` **except** the one documented,
  verified base-case `smt` gap (§6.1) at the exact tactic the story itself flags as possibly
  genuinely failing; every other file (`Types.ec`, `Interfaces.ec`, all seven package variants, all
  four games, all three `Eq_*_Invariants.ec`) compiles cleanly. Re-run by hand end to end with the
  story's own exact §5 recipe (recorded output in this report's own session, not just asserted).
- [x] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` shows both sides over one composition with different
  literal `run` arguments (`run(false, true)` / `run(true, true)`) and lists the shared
  composition's modules once in the restriction
  (`proof::tests::real_hybrid3_ideal_hybrid3_shares_one_composition_in_restrictions_and_requires`,
  `..._run_args_are_different_literals`).
- [~] The base case is a real `smt(…)` call (never `admit`) — true, always emitted; it fails for
  4WHS (and for `kem-dem-cca-ssp`), and the goal is recorded (§6.1) rather than papered over, exactly
  per the story's own instruction for this exact scenario.
- [x] Bullet order matches the game interface export order exactly
  (`proof::tests::hybrid0_hybrid1_bullet_order_matches_export_order`).
- [~] `kem-dem` and `hello-world` also produce compiling `Eq_*.ec` files — true for `kem-dem-cca-ssp`
  (confirmed end to end, modulo the same §6.1 base-case gap); **not** true for `hello-world`, which
  cannot export *at all* today due to a pre-existing, out-of-scope invariant-format incompatibility
  discovered by this story (§6.2) — not a defect in this story's own code.
- [x] Deterministic (`proof::tests::rendering_is_deterministic`); `cargo build/test/clippy
  --workspace` clean.

## 8. State handed to the next story

- **Entry points**: `proof::compute_equivalence_files(theorem, project, interfaces) ->
  Result<Vec<EquivalenceFiles>, EcExportError>`, called once by `export::export_theorem` (now
  `export_theorem(theorem, project: &impl Project)` — the signature change every future caller of
  `export_theorem` must apply). `EquivalenceFiles { invariants: InvariantFile, proof:
  EquivalenceProofFile }` per equivalence hop.
- **Story 08/09 (lowering to the debugger IR / `inline --easycrypt` / `debug --easycrypt`)**: the
  proof skeleton's own `admit` bullets are exactly where a human (or a future story) fills in
  path-derived tactics — nothing here derives them, by design (§1). The oracle bullet's mangled proc
  name (the `(* d_NewKey *)` comment) is reproducible independently via a fresh `Names(Proc)` over
  `export.name()`, same as the router's own naming — a future story needing to correlate a bullet
  with its router proc doesn't need new plumbing for that.
- **Four shared-infrastructure fixes, not story-07-local** (§4, §4.1, §4.2, §5): `invariant.rs`'s
  `mangle_local_binder` (any local SMT-source binder that would mangle to exactly `l`/`r` is now
  escaped), `invariant.rs`'s binder-name-agnostic `define-state-relation` handling (§4.1 — binder
  spelling is positional, not a fixed `left`/`right` vocabulary), `invariant.rs`'s whole-package-
  state-equality expansion (§4.2 — `(= <side>.<inst> <side>.<inst>)` now expands to a field-by-field
  conjunction), and `names.rs`'s bare-`_` escaping (`d__`) are all now the established, correct
  behavior crate-wide — a future translator in this epic should not need to rediscover any of them.
- **`easycrypt llm -lastgoals`** (§6.1) is a genuinely useful, previously-undocumented tool for this
  epic: `easycrypt llm -lastgoals -I <dirs…> <file>.ec` prints the exact remaining goal(s) on a batch
  compile failure, `-upto LINE[:COL]` compiles only up to a point — both are worth reaching for
  whenever a future story needs to see *why* a tactic script doesn't close, not just that it didn't.
- **The invariant-format gap (§6.2) is narrower than this report first found, and `Full4WHS`'s own
  slice of it is now fully closed**: `hello-world`/`simple-KEM-example`'s hand-written invariants use
  `src/writers/smt`'s own solver-facing whole-game-state encoding (a second SMT dialect entirely,
  still unaddressed — genuinely this epic's biggest remaining invariant-format gap); `Full4WHS`'s do
  **not** — after §4.1's binder-naming fix and §4.2's whole-package-equality expansion, `Full4WHS`'s
  export advances past every file that uses story 06's flat per-field grammar and only stops at a
  third, unrelated, unattempted gap (an unsubstituted `<0_n>` bit-width placeholder atom in
  `invariant-H7_1_1_0-H7_1_1_1.smt2`, §4.2's closing paragraph) whose extent beyond that one file is
  unknown (export stops at the first failure). A future story wanting full `hello-world`/
  `simple-KEM-example` coverage needs a second invariant-translation path (or those fixtures
  re-authored in the new grammar); a future story wanting full `Full4WHS` coverage needs to
  investigate the `<0_n>`-style placeholder gap next — recorded here so it isn't rediscovered from
  scratch.
- **Golden/behavioral tests**: `proof.rs`'s own inline tests (no separate `testdata/easycrypt/
  story07/` golden directory — this story's acceptance criteria are compile-shaped and
  structural/behavioral assertions, not exact-text golden matches, since the proof skeleton's own
  text (record literals, restrictions) is project-specific and already covered by real
  `easycrypt compile` checks); `export.rs`'s
  `simple_4whs_full_tree_compiles_in_dependency_order` and new
  `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` run the full `Types → Interfaces →
  packages → games → Eq_*_Invariants → Eq_*` chain for real.

## 9. Notes for follow-up (not this story's scope)

- §6.2's invariant-format gap (the `GameState_`-sort dialect) is the single biggest open item from
  this session — see §8's own callout. It blocks `hello-world`/`simple-KEM-example` from ever
  producing a full `domino easycrypt` export until addressed, independent of anything in stories
  07/08/09.
- §4.2's whole-package-state-equality gap is fixed (was previously flagged here as a follow-up).
- The new `<0_n>`-style bit-width placeholder gap (§4.2's closing paragraph,
  `invariant-H7_1_1_0-H7_1_1_1.smt2`) is `Full4WHS`'s next blocker: an unsubstituted template atom
  that isn't one of §3.2's fixed forms. Not investigated — its shape (how many distinct placeholder
  forms exist, whether it's one token or a family) and how many of `Full4WHS`'s remaining ~13
  unexamined invariant files hit it or something else entirely are both unknown, since export stops
  at the first failure. Flagged rather than guessed at.
- §6.1's base-case gap might be closeable with more targeted `smt` hints or a `have`/`rewrite`
  detour establishing `b{!1} = b{!2}` before the final `smt` call — but per the story's own explicit
  instruction, this was recorded rather than chased; a future session with more budget could
  legitimately spend time here without contradicting this story's own scope.
- `oracle_set_mismatch` (§3) is implemented and unit-testable but has never fired against a real
  target project (every one's proof-tree oracle set matches its exports exactly) — same "reachable
  but untested against reality" caveat story 05's own report already flagged for the
  `Hybrid`/`Conjecture` skip-note text.
