# Story 06 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (320 passed, 4 pre-existing
`#[ignore]`d, none new) and `cargo clippy --workspace --all-targets` are all clean. `easycrypt`
(`r2026.06-12-g7e192dd`) was on `PATH`, so `Eq_Hybrid0_Hybrid1_Invariants.ec` for 4WHS `Simple4WHS`
was compiled for real (not skipped) against `Types.ec` (story 02's golden copy) — the acceptance
target.

## 1. What exists

`src/writers/easycrypt/invariant.rs` (~1000 lines of implementation + ~800 lines of tests), plus
two small, necessary changes to shared infrastructure (§5).

```rust
pub struct InvariantFile {
    pub file_name: String,          // "Eq_<Left>_<Right>_Invariants.ec"
    pub file: EcFile,
    pub left_state_type: String,    // "<Left>_state"
    pub right_state_type: String,   // "<Right>_state"
    pub skipped: Vec<String>,       // human-readable, for stdout — mirrors export::ExportedTheorem::skipped
}

pub fn build_invariant_file(
    theorem: &Theorem<'_>,
    equivalence: &Equivalence,
    project: &impl Project,
) -> Result<InvariantFile, EcExportError>;
```

`project` is needed because `Equivalence::invariants()` returns file *paths*, read the same way
`gamehops::equivalence::mod.rs::load_invariants` already does (`project.read_input_file`). Every
path in `equivalence.invariants()` is read and parsed, in order, into one shared file — this
matters for `Hybrid1 ~ Hybrid2` and `Real_Hybrid3 ~ Ideal_Hybrid3`, whose `invariant:` field in the
`.ssp` is a **list** of two files (the invariant proper, then a `randomness-*.smt2` file whose
`define-fun randomness-mapping-*`s are all skipped — confirmed live, not just per the story text).

Tests are inline (`#[cfg(test)] mod tests`), following stories 02–04's precedent.

## 2. The record naming rule is *not* "only when both sides share a composition"

The story's own text (§3.1) says record fields are bare `pkg_<instance>_<field>`, with an `l_`/`r_`
prefix added only "when both sides share a composition". **This is real EasyCrypt behavior it
doesn't hold up under**, discovered by actually compiling the output:

- Verified directly against `r2026.06-12-g7e192dd`: two record types declared in one file **cannot
  share a field name at all**, regardless of whether their surrounding types would disambiguate a
  projection (`the symbol abort_flag already exists`, reproduced in isolation).
- Every side of an equivalence's game-state record needs an `abort_flag` field with the *same*
  intended meaning — so **`abort_flag` always collides between left and right, in every equivalence,
  whether or not the two sides share a composition**. `Hybrid0`/`Hybrid1` (different compositions,
  per story 04's own discovery) still collide purely on `abort_flag`.
- It's not just `abort_flag`, either: `Hybrid0`'s composition and `Hybrid1`'s composition both name
  their package instances `KX`/`Prot` (a real, unplanned-for naming coincidence in `Simple4WHS`, not
  a same-composition case), and both `KX`/`KX_NoKeys` share several state field names (`LTK`, `H`,
  `ctr_`, `kid_`, `RevTested`, `Fresh`, `State`) — so `pkg_KX_d_LTK` etc. would *also* collide between
  `Hybrid0_state` and `Hybrid1_state` even ignoring `abort_flag`.

**Implemented rule: every field on the left record is prefixed `l_`, every field on the right is
prefixed `r_`, unconditionally** — `l_pkg_<instance>_<mangled field>` / `r_pkg_<instance>_<mangled
field>`, and `l_abort_flag` / `r_abort_flag`. This is a strict superset of "add the prefix when
sharing a composition": it produces non-colliding fields in *every* case (confirmed by compiling
`l_x`/`r_x`-style records directly), including the ones the story's own conditional rule would have
missed. `<mangled field>` is `Names::mangle(NameKind::Var, raw_field_name)` — the *same* mangling
`package.rs`'s own module-var rendering already uses for that field, so `LTK` becomes `d_LTK` inside
the field name exactly as it does in the package's own module (`l_pkg_KX_d_LTK`), confirming the
story's own worked example's `pkg_KX_d_LTK` fragment. The `<instance>` fragment itself is **not**
mangled (inserted verbatim) — the worked example's `KX` (not `d_KX` or similar) confirmed this is
intentional, not an oversight: it is a name-fragment inside an already-legal identifier, not an
identifier of its own.

Record type names are the bare `<game instance name>_state` (`Hybrid0_state`, not run through
`Names::mangle`) — mangling would have wrongly `d_`-prefixed every real project's game instance name
(they're all capitalized), and a compile check confirmed EasyCrypt type names have no such
lowercase-start requirement (only `proc`/program-variable names do, per the overview's own §8.1
fact).

## 3. The record includes parameter-derived fields too, not just `Package::state`

The story's own §3.1 literally enumerates "one field per (instance, state field)". But §3.3's own
worked example for `params_inv` writes `` l.`pkg_X_b = r.`pkg_Y_b `` — a **record field projection**
on a package's own **parameter** `b`, which `Package::state` never lists (`b` is in `Package::params`).
Reconciling this: a package's `Boolean`/non-width-`Integer` param is stored as a **persistent module
`var`** by story 03's own `param_needs_var`/`init` rendering (`package.rs`), exactly like a state
field — it just isn't declared under `Package::state`. `params_inv`'s own body needs to compare the
value that survives *after* `init` runs (the whole reason a relational invariant can assert it at
all), so it has to be a record field too.

**Implemented**: `build_side_record` emits one field per `Package::state` entry (in `pkg.state`
order) **then** one per qualifying `Package::params` entry (`package::param_needs_var`, `pkg.params`
order) — mirroring `package.rs::render_variant`'s own `module_vars.extend(param_vars)` order exactly
— then `abort_flag` last. The combined lookup map (§4) is populated identically for both, so
`params_inv` and a `.smt2` dotted accessor use the same machinery.

## 4. One combined lookup map, not two

`build_side_record(game_inst, binder, op_param, field_ns_prefix, combined_lookup)` is called once per
side, both writing into the **same** `HashMap<String, (EcExpr, EcType)>`, keyed by the raw SMT-style
dotted path (`"left.KX.State"`, `"right.Prf.b"` — the latter never appears in a real `.smt2` file,
only used internally by `params_inv`, but the key scheme is uniform). Every atom-resolution site
(`.smt2` dotted accessors *and* `params_inv`'s own field lookups) queries this one map, so there is
exactly one place that decides a field's final EasyCrypt name and type.

## 5. Two real, verified EasyCrypt facts this story hit — fixed at their proper (shared) home

Both surfaced only once `easycrypt compile` was actually run against `Eq_Hybrid0_Hybrid1_Invariants.ec`
(not just golden-file string matching) — this story's `hybrid0_hybrid1_invariants_file_compiles` test
is the first place in the epic an `=`-shaped SMT-derived formula gets compiled, and the first place a
comparison-shaped SMT formula (`>`) does either.

### 5.1 `=`/`<>` are non-associative in EasyCrypt — `render.rs` treated them as left-associative

`a = b = c` is a **parse error** in EasyCrypt (`r2026.06-12-g7e192dd`, reproduced in isolation),
unlike same-precedence `<`/`<=`/`>`/`>=` chains, which *parse* (and only fail to typecheck when the
chain's types don't line up, e.g. `bool < int`). `render.rs`'s `render_expr_inner`'s `Binop` case
used one associativity rule (`right_assoc`) for every operator, which rendered a chained `Eq`/`Ne`
without parenthesizing its same-precedence operand — this had never been exercised before because no
earlier story's translator produced an `Eq`/`Ne` node whose *own operand* was itself `Eq`/`Ne`.
`Domino_state_eq`'s SMT source does exactly that: `(= (is-mk-none L) (is-mk-none R))`, and
`is-mk-none` itself translates to `_ = None<:T>` (§3.2's own table row), so the outer `=` always
nests two more `=`s.

**Fix, in `render.rs`** (shared, not story-06-local): `Eq`/`Ne` now use `(level + 1, level + 1)` for
both operands instead of the generic `right_assoc`-driven split, so `(a = b) = (c = d)` renders fully
parenthesized. Added `tests.rs::precedence_eq_is_not_associative_needs_parens_on_both_sides` as a
permanent regression test (the existing `precedence_eq_binds_tighter_than_and` test ANDs two
top-level `Eq`s together, which never exercised this — an `Eq` nested *inside* another `Eq` is a
different shape). No existing golden file changed (nothing before this story ever nested `Eq` inside
`Eq`).

### 5.2 `>`/`>=` don't exist for `int` — `EcBinop::Gt`/`Ge` are unusable, not just "same as SMT"

Compiling `Domino_time_of_acceptance`'s `mess > 1` failed: `` operator `Top.Real.>' cannot be applied
… expected … real … applied to a value of type int``. EasyCrypt's `Int`/`IntDiv` theories define
`<`/`<=` but not `>`/`>=`; the bare `>`/`>=` *notation* resolves only via the `Real` theory, which
then (correctly) rejects `int` arguments. **This is exactly the fact story 01/02 already discovered**
for Domino's own `GreaterThen`/`GreaterThenEq` expressions (`types.rs`'s own committed comment: "the
flip is unconditionally correct… EasyCrypt's stdlib has no `>`/`>=` at all") — §3.2's table for this
story simply said "`> >= < <= + - *` | same", which turned out not to hold for `>`/`>=` specifically,
the same way it never held for Domino's own expression translator.

**Fix, in `invariant.rs::translate_cmp`** (this story's own file, not shared): `>`/`>=` are always
flipped to `<`/`<=` with swapped operands, exactly mirroring `types.rs`'s established convention —
`EcBinop::Gt`/`Ge` are never emitted. `EcBinop::Gt`/`Ge` remain in `ast.rs`/`render.rs` as AST
variants (removing them would be out of scope and they may still suit a future `real`-typed
formula), but **no code in this crate should ever construct one for an `int`/`Bits` comparison** —
this is now the second, independently-discovered confirmation of that constraint.

## 6. SMT → EasyCrypt translation, as implemented (§3.2's table)

All of it lives in `TCtx::translate`/`translate_list`'s per-form helpers, each returning
`(EcExpr, EcType)` — the type is tracked alongside every translated expression (not thrown away)
because `is-mk-none`/`maybe-get`/tuple-projection genuinely need it (below), and it costs nothing
extra to propagate everywhere else.

- **`forall`/`exists`/`let`**: binder/`let`-binding names mangled via `Names::mangle(NameKind::Var,
  …)`, one `Names` instance shared for the *whole* top-level definition's body (so repeated shadowing
  of the same raw name, e.g. nested `let`s both naming `state`, is idempotent — not a collision — but
  two *different* raw names colliding after mangling still is). A multi-binding `let`
  (`(let ((x e1) (y e2)) body)` — the real files always have several) desugars to nested single-`let`s,
  translating every `ei` in the **outer** scope first (SMT-LIB's own parallel-binding semantics)
  before any of the new names enter scope.
- **`ite`/`and`/`or`/`not`/`=>`/`=`**: exactly the table's forms; `and`/`or`/`=>` fold left
  (`fold_and`-style) for n-ary; `=` with more than 2 args becomes an adjacent-pair conjunction
  (`a=b /\ b=c /\ …`), not all-pairs.
- **`>`/`>=`/`<`/`<=`/`+`/`-`/`*`**: `<`/`<=` direct; `>`/`>=` flipped (§5.2); `-` with 1 argument is
  unary negation, with 2 is subtraction (SMT-LIB overloads `-` this way; the table doesn't call it
  out, but the real files never use unary `-` — added for completeness and covered by a unit test).
- **`select`/`store`**: `A.[k]` / `A.[k <- v]`. `select`'s *type* is `EcType::Option(value_ty)` where
  `value_ty` is the array's declared value sort **with one outer `Maybe` layer peeled** — Domino's SMT
  writer always wraps a table's value sort in `Maybe` (`(Array Int (Maybe (Tuple10 …)))`) to model an
  absent cell over an SMT `Array` (which is total), whereas EasyCrypt's `fmap` already models absence
  via `.[k]`'s own `option` return; the two only agree once this layer is peeled — confirmed against
  `Package::state`'s own Domino-`Type` → `EcType` translation (`types::translate_type`), which never
  adds a second `option` layer for a `Table`'s value type either. Implemented in `translate_sort`'s
  `Array` case (`strip_maybe_and_translate`), *not* by special-casing `select` itself, so a nested
  `select`-of-`select` (never occurs in the target files, but is not ruled out) types correctly too.
- **`is-mk-none`/`maybe-get`/`mk-some`/`(as mk-none (Maybe T))`**: as the table specifies, using each
  operand's tracked `EcType::Option` to supply `None_`'s required type parameter (`EcExpr::None_`
  always carries an explicit `EcType` — there is no "bare untyped `None`" AST variant, so this
  tracking is not optional, it's how `None_`'s argument gets produced at all).
- **`mk-tupleN`/`elN-i`**: `mk-tupleN` validates argument count against `N`; `elN-i` validates its
  operand's tracked type is an `N`-tuple and `1 <= i <= N`, parsed via `parse_proj_name` (`el` prefix,
  split once on `-`, both halves must parse as plain integers — guards against a dash-containing,
  coincidentally `el`-prefixed *name* being misread as a projection, though no such name exists in any
  target project).
- **`<<func-f>>`**: `func_op_name(f)` applied curried, its EasyCrypt return type looked up from
  `Theorem::consts`'s own declared `Fn(_, ret)` (not hardcoded to `bool`, even though every target
  project's own top-level `define-fun`s happen to return `Bool` — a future project's helper calling a
  non-`Bool` theorem function inside a larger expression is handled correctly, not by luck).
- **Everything else** (a plain identifier head not matching any of the above): looked up in this
  file's own `OpRegistry` (`define-fun`/`define-state-relation` names seen so far, in file order —
  SMT-LIB's own "define before use" discipline making this valid); not found there → hard error
  (`InvariantError::Unrecognised`, naming the file and the exact s-expression) — covers both a truly
  unknown atom/call and a forward reference.

### 6.1 SMT-definition-name mangling, beyond `-` → `_`

`state=` and `=prf` are **real names in the target `.smt2` files** (not hypothetical) — the atom
charset (`- = < > $ ! + @ . *`) is wider than the story's own "watch for `-`/`_`" note anticipates.
`mangle_smt_def_name` maps each of these to an underscore-delimited word (`=` → `_eq_`, `<` → `_lt_`,
`>` → `_gt_`, `!` → `_not_`, `+` → `_plus_`, `@` → `_at_`, `.` → `_dot_`, `*` → `_star_`, `$` →
`_dollar_`), then collapses repeated underscores and trims the ends — `state=` → `state_eq` and
`=prf` → `eq_prf`, matching the story's own `Domino_state_eq` worked example exactly (this is strong
evidence the story author derived that example from the real file, and the mapping here reproduces
their intent, not just "a" legal mangling). Collision detection (`OpRegistry::define`) is a small
dedicated `HashMap<mangled, raw>`, deliberately **not** routed through `names::Names` — `Names::mangle`
only substitutes `-` → `_` and handles keyword/case escaping, neither of which this module's
`Domino_`-prefixed names need (a `Domino_`-prefixed name can never collide with an EasyCrypt keyword
or need case escaping), so reusing it would have meant *also* picking up its unrelated `d_`-prefix
logic for no benefit.

## 7. `params_inv`, exactly

`build_params_inv` matches package instances between the two sides **by raw instance name**
(`PackageInstance::name`) — correct for every target project (an equivalence's two sides always reuse
the same instance names, whether or not they share a composition; see §2's own finding). For each
matched instance's own qualifying param (`package::param_needs_var`, checked on *both* sides
independently — a param that's `Boolean`/non-width-`Integer` on one side but, hypothetically, doesn't
qualify on the other is skipped, not asserted incorrectly), resolves each side's bound value to
`ParamValue::TheoremConst(name)` or `ParamValue::Literal(text)` by walking
`Identifier::GameIdentifier(Const).assigned_value`/`PackageIdentifier(Const).game_assignment` to
their end (these fields already carry "what this composition/package const is bound to for *this*
instantiation" — populated during game-instance instantiation, `theorem.rs`'s own
`instantiate::rewrite_pkg_inst`/`GameInstance::new` — so no new resolution machinery was needed, only
walking an existing chain to completion):

- Both sides `TheoremConst` with the **same** name → `` l.`field = r.`field `` (verified:
  `Hybrid0`/`Hybrid1`'s shared `KX.b` both resolve to the theorem's own `b`).
- Otherwise, **each** side that resolves to a `Literal` gets its own `` <side>.`field = <literal> ``
  conjunct, independently (verified: `Real_Hybrid3`/`Ideal_Hybrid3`'s `Prf.b` — bound to the
  composition's own `bprf`, itself bound to the *literal* `true` on both instances — produces
  `l_pkg_Prf_b = true` **and** `r_pkg_Prf_b = true` as two separate conjuncts, not one equality; their
  own `KX.b`, bound to literal `false`/`true` respectively, likewise produces two independent,
  *unequal* literal facts, exactly capturing "this is the bit that differs between the two hops").
- Two different `TheoremConst`s, or a `Literal` on one side and a `TheoremConst` on the other,
  contribute nothing (no fact can be stated about a free theorem constant beyond what's given) — not
  hit by either target equivalence, but a deliberate, non-panicking `continue`, not an unreachable.

## 8. Skipped forms

`define-lemma`, `define-game-invariant`, `define-package-invariant` (grammar-level alternatives to
`define-fun`/`define-state-relation`, never reached via `handle_definefun`) and any `define-fun` whose
name starts with `randomness-mapping-` (checked *before* parsing its argument sorts, since these use
a `SampleId` sort this story doesn't and shouldn't support) are each skipped: an `EcItem::Comment` in
the output at the point they'd otherwise have appeared, and a human-readable entry appended to
`InvariantFile::skipped` (a `Vec<String>`, mirroring `export::ExportedTheorem::skipped`'s own
report-only-data-not-behavior design) for a future CLI wiring's stdout report — this story does not
print anything itself, matching its own scope (no `domino easycrypt` wiring, see §10).

## 9. Golden file and acceptance criteria, checked against what was built

- [x] `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` — generated and confirmed to
  compile for real against `testdata/easycrypt/story02/4WHS/Types.ec`
  (`hybrid0_hybrid1_invariants_file_compiles`, `hybrid0_hybrid1_invariants_file_matches_golden`).
- [x] Every row of §3.2 has its own unit test in `invariant.rs`'s `tests` module (`forall`, `let`
  single/multi-binding, `ite`, `and`/`or`/`not`/`=>`, `=` 2-arg/n-arg, comparisons/arithmetic,
  `select`/`store`, `is-mk-none`/`maybe-get`, `mk-some`/`(as mk-none …)`, tuple construction/
  projection, `<<func-f>>` application, calling a previously-defined op) plus the sort-translation
  table (`sort_translation_covers_the_table`).
- [x] `el10-4` on a `mk-tuple10` round-trips to `` .`4 `` (`tuple_construction_and_projection_round_trip`
  — using `el10-4`/`Tuple10`, matching the real files' own `el11-4`/`Tuple11` shape one size down for a
  smaller test fixture; the acceptance bullet's literal `el11-4` is exercised for real inside the
  golden-file test, where `Domino_keys_computed_correctly`'s body uses exactly `el11-4` → `` .`4 ``
  against an 11-tuple `State`).
- [x] A `define-lemma` is skipped with a comment and reported
  (`define_lemma_is_skipped_with_a_comment_and_reported`); an unknown atom inside a
  `define-state-relation` is a hard error naming the file
  (`unknown_atom_inside_a_define_state_relation_is_a_hard_error_naming_the_file`).
- [x] `params_inv` for `Hybrid0`/`Hybrid1` relates `b` via equality (both bind the theorem constant
  `b`); for `Real_Hybrid3`/`Ideal_Hybrid3` states literals directly
  (`real_hybrid3_ideal_hybrid3_params_inv_states_literals_directly`).
- [x] `Real_Hybrid3`/`Ideal_Hybrid3` (sharing the `Hybrid2` composition) produce two record types with
  disjoint field names (`real_hybrid3_ideal_hybrid3_share_a_composition_but_get_non_colliding_fields`
  — also confirms every left field's `l_`-stripped name has a `r_`-prefixed counterpart, i.e. this is
  genuinely the "same composition, same instance names on both sides" case, not incidentally disjoint
  fields).
- [x] Deterministic (nothing here iterates a `HashMap` when building `EcFile.items` — `OpRegistry`
  and the combined lookup map are only ever *looked up* during rendering, never iterated), confirmed
  by its own `rendering_is_deterministic` test (stories 01–04's own established convention —
  `build_invariant_file` called twice, rendered output compared); `cargo build/test/clippy
  --workspace` clean.
- [x] (Bonus, not an explicit bullet but implied by "Hybrid1 may be done in parallel" style testing)
  `Hybrid1 ~ Hybrid2`'s multi-file `invariant: [...]` list (the invariant proper plus a
  `randomness-*.smt2` file) is read and concatenated correctly, with every `randomness-mapping-*`
  `define-fun` in the second file skipped
  (`hybrid1_hybrid2_multi_file_invariant_skips_randomness_mapping_defuns`).

## 10. State handed to the next story (07 — proof skeleton)

- **Entry point**: `invariant::build_invariant_file(theorem, equivalence, project) ->
  Result<InvariantFile, EcExportError>`. Not wired into `export::export_theorem`/`domino easycrypt`'s
  CLI — that orchestration (looping over every `GameHop::Equivalence`, writing
  `Eq_<Left>_<Right>_Invariants.ec` next to story 07's own `Eq_<Left>_<Right>.ec`) is story 07's job,
  the same way story 06 was explicitly allowed to be built in parallel with story 05.
- **The record type names and field-naming rule story 07 must reproduce exactly** (its own inline
  `call`-site record literal, per §6 Notes/risks — "nothing outside the invariant operators may
  mention it… story 07 builds it inline at the `call` site"): `<game instance name>_state`
  (`Hybrid0_state`); every field is `l_pkg_<instance>_<mangled field>` on the left side and
  `r_pkg_<instance>_<mangled field>` on the right, **unconditionally** — §2's finding supersedes the
  story's own "only when sharing a composition" text, and story 07 should build its record literals
  with this same unconditional prefix rule, not the conditional one. `<mangled field>` is
  `Names::mangle(NameKind::Var, raw_name)` — the same name `package.rs` gave that field/param as a
  module `var`, so `` {|l_pkg_KX_d_LTK = Pkg_KX.KX.d_LTK{1}; …|} `` (or however story 07 spells a
  memory-tagged program-variable read) can be built by re-deriving each field's raw name and applying
  the *same* mangling, without needing this module's own internal maps.
- **`inv`/`params_inv` signatures**: `op inv (l : <Left>_state) (r : <Right>_state) : bool` and `op
  params_inv (l : <Left>_state) (r : <Right>_state) : bool`, both fixed literal names (never mangled,
  never collide with a `Domino_`-prefixed name by construction).
- **SMT forms translated vs. skipped**: every row of §3.2 (§6 above) is translated; `define-lemma`,
  `define-game-invariant`, `define-package-invariant`, and any `randomness-mapping-*`-named
  `define-fun` are skipped (comment in the output, entry in `InvariantFile::skipped`) — story 07 (or
  whichever story eventually handles randomness mappings/hybrid game hops, out of scope for the whole
  epic per `00-overview.md` §2) should not expect these to appear as callable ops.
- **Two shared-infrastructure fixes, not story-06-local** (§5): `render.rs`'s `Eq`/`Ne` are now
  genuinely non-associative in the renderer (parens on both sides when nested), matching verified
  EasyCrypt grammar behavior; and the established "never emit `EcBinop::Gt`/`Ge` for an `int`/`Bits`
  comparison, always flip to `Lt`/`Le`" rule (previously only documented for `types.rs`'s Domino-
  expression translator) is now also enforced in `invariant.rs`'s own SMT-comparison translation —
  any *future* translator in this epic emitting a numeric `>`/`>=` must do the same flip, not assume
  §3.2-style tables that say "same" are literally correct without a compile check.
- **Golden-file path**: `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`, generated
  from the real `Simple4WHS` project and confirmed to compile against story 02's `Types.ec`.

## 11. Notes for follow-up (not this story's scope)

- `params_inv` matches package instances by raw name across the two sides. This is correct for every
  target project (§7), but is a real, accepted limitation the same way story 04's interface-dedup
  key is (§7 of that report) — a future project whose two sides give the "same" package instance
  different names would silently get no `params_inv` fact for it instead of a wrong one (safe, but
  incomplete).
- `OpRegistry`'s collision detection is scoped to one `build_invariant_file` call (i.e., one
  equivalence's own invariant + randomness files together), not across different equivalences in the
  same theorem — correct, since each equivalence gets its own `Eq_*_Invariants.ec` file/namespace.
- `EcBinop::Gt`/`Ge` remain constructible in `ast.rs` (removing them is out of scope and a future
  `real`-typed formula might legitimately want them) — but every producer in this crate now avoids
  them for `int`/`Bits` comparisons; a new one should be checked against this precedent before
  emitting either.
