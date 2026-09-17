# Story 14 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (348 passed, 5 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`~/.opam/easycrypt/bin/easycrypt`, `r2026.06-12-g7e192dd`) was on `PATH`, so every
compile-shaped test — including the three `*_full_tree_compiles_in_dependency_order` tests — ran
for real, not skipped.

## 1. What changed

### 1.1 The variant key (§3.1) — `package.rs`

`VariantKey` lost its `imports: Vec<(Vec<String>, Box<VariantKey>)>` field entirely. `compute_key`
no longer takes a `computed: &[Option<VariantKey>]` accumulator or needs `ordered_pkgs_idx()`
sequencing — `compute_all_keys` is now `(0..comp.pkgs.len()).map(compute_key).collect()`, computing
every instance's key independently. `int_params` keeps an entry only when
`integer_param_used_as_width` is true for that param; a non-width integer param (already a module
`var` via `param_needs_var`) no longer distinguishes two instances.

### 1.2 A package's own import interface (§3.2) — `package.rs`

`render_variant` builds `<Variant>_Imports` from `pkg.imports` via two new functions:
`ordered_imports` (see §2 below — **not** simply `&pkg.imports`) and `build_import_procs`
(the shared proc-signature shape, moved out of the now-deleted `interfaces.rs::build_variant_procs`).
`PackageScope` lost its `functor_params: HashMap<usize, String>` field — the functor parameter is
always `O`, so there is nothing left to look up. A package with no imports gets neither the module
type nor a functor parameter, unchanged from before. `require Interfaces` is gone from every
package file; the only `require import` is `Types` (plus the stdlib theories).

### 1.3 Bodies call the import name (§3.3) — `package.rs`

`translate_invoke`: `module` is now the literal string `"O"`; `proc` is
`Names::new().mangle(NameKind::Proc, edge.name())` (was `edge.sig().name`). This is the one place
this story changes generated *oracle bodies*, not just wiring — confirmed by
`hello_world_oracle_rename_new_medium_composition_gets_one_adapter_using_import_names` (§4 below)
and by `Pkg_Fwd.ec` calling `O.d_ChangeNameUsefulOracle`/`O.d_AnotherUsefulOracle`, never
`O.d_UsefulOracle`.

### 1.4 Clones, instances, adapters (§3.4) — `game.rs`

Every instance now gets, unconditionally: `clone Pkg_<Variant> as Cloned_Pkg_<inst>.`, then either a
direct `module Pkg_Inst_<inst> = Cloned_Pkg_<inst>.<Variant>.` (no imports) or, when it does,
`module Pkg_Inst_<inst> = Cloned_Pkg_<inst>.<Variant>(<arg>).` where `<arg>` is either
`Pkg_Inst_<callee>` (direct pass) or a freshly-built `Pkg_Imports_<inst>` adapter module (emitted
immediately before it). `direct_pass_callee` implements the exact §3.4 rule: `Some(callee)` iff
every edge out of the instance shares one callee and none is aliased; `None` (⇒ adapter) otherwise.
`build_import_adapter` emits one stateless forwarding proc per import, ascribed to the **uncloned**
`Pkg_<Variant>.<Variant>_Imports` (§2.1 row 2). `module_ref`'s old two-stage
"dotted-path-then-maybe-upgraded" bookkeeping is gone — every call site, everywhere in the file
(router `init`, export procs), just reads `inst_module_name[idx]` (`Pkg_Inst_<inst>`), computed once
up front.

### 1.5 `Interfaces.ec` holds game interfaces only (§3.5) — `interfaces.rs`

Deleted: `build_variant_procs`, the whole package-variant grouping/aliasing loop (story 11's
section), and its two unit tests. `discover_compositions`, `build_export_procs`,
`comp_mangled`/`iface_name`/`adv_name` are untouched, confirmed by grep and by
`simple_4whs_hybrid0_and_hybrid1_reuse_one_interface`/`simple_4whs_prf_has_its_own_interface`
passing unchanged. Replaced the two deleted story-11 tests with
`no_module_type_in_interfaces_is_a_package_variant`, which asserts every `module type` line in a
rendered `Interfaces.ec` starts with `Iface_` or `Adv_`.

This **supersedes story 11**, which improved the readability of a section that no longer exists —
story 11 was not wrong; the section it deduplicated is simply gone.

### 1.6 The prefix rename (§3.6)

- `export.rs`: `Variant_{}.ec` → `Pkg_{}.ec`.
- `game.rs`: `Pkg_<inst>` → `Cloned_Pkg_<inst>`, `Inst_<inst>` → `Pkg_Inst_<inst>` (now
  unconditional), clone `base` / `require` list `Variant_<V>` → `Pkg_<V>`.
- `proof.rs`: `restrictions_for` and `build_side_record_lit` now name `Pkg_Inst_<inst>` directly,
  with **no** variant-name component. `CompLayout.variant_names` and the `variant_name_map`
  parameter threaded into `compute_layout`/`build_equivalence_file`/`compute_equivalence_files` are
  all **deleted outright** — nothing in `proof.rs` needs a variant's name at proof-writing time any
  more (§7's open question, answered: gone, not "still needed").
- `invariant.rs`: confirmed zero changes needed (builds record types and field names, never module
  paths) — grepped for `Variant_`/`Pkg_KX`/bare `Inst_`, no hits.
- Module-level doc comments updated: `game.rs:3-19`, `package.rs:173-176`, `interfaces.rs:3-17`,
  `export.rs:3-8`, `ast.rs:148,277`.

## 2. A real bug this story's own design assumption didn't anticipate, and how it was fixed

§3.2/§3.4 both say "one proc per `pkg.imports` entry, **in declaration order**". That's false as a
property of `Package::imports: Vec<(OracleSig, SourceSpan)>` — its element order is **not**
deterministic across two independent parses of the same project (a parser-internal characteristic,
unrelated to this epic; pre-story-14 code never iterated `pkg.imports` directly for anything
rendering-shaped, only `comp.edges`, which *is* a stably-ordered `Vec`). Every other story-14
acceptance criterion passed on the first real run; `cargo test --workspace`'s
`game::tests::rendering_is_deterministic` and `export::tests::rendering_is_deterministic` did not —
confirmed as a genuine regression (not pre-existing flakiness) by running the identical tests
against a clean pre-story-14 worktree five times, all green, then instrumenting the failing run and
finding `Simple4WHS`'s `KX` package's `pkg.imports` list (`Run1`..`Run5`, `Eval`, `Hon`) in two
different orders across two `export_theorem` calls in the same process.

Fix: `package::ordered_imports(pkg: &Package) -> Vec<&(OracleSig, SourceSpan)>`, sorted by
`sig.name`. Import names are unique per package (§2.2's uniqueness guarantee, one level up from
"unique per instance" — a package's own declared list can't repeat a name either, or two of its own
imports would be indistinguishable to every caller), so sorting by name is an unambiguous,
deterministic canonicalisation, not a heuristic. Both `package.rs::build_import_procs` (the
interface) and `game.rs::build_import_adapter` (any adapter satisfying it) call it, so an adapter's
proc order always matches the interface it ascribes to, independent of whatever order the parser
happened to hand back. Confirmed: `rendering_is_deterministic` in `game.rs`, `export.rs`,
`interfaces.rs` and `proof.rs` all green, five consecutive runs each, after the fix; the goldens
below were captured *after* this fix (an earlier capture, before it, would have been correct exactly
once and then unreproducible).

**This is worth a story of its own to actually fix at the parser level** (make `Package::imports`'s
own construction preserve source order) — out of scope here; the writer-side canonicalisation is a
complete, correct workaround, not a partial one, since the epic never needs the *literal* source
order, only *a* stable one that the interface and every adapter agree on.

## 3. `hello-world-oracle-rename-new` — deviated from the story's literal worked example

§3.7 describes this project's `MediumComposition` as already having `fwd: {
ChangeNameUsefulOracle: UsefulOracle of fwd, AnotherUsefulOracle: UsefulOracle of rand }`. That
text does not match what was on disk: the project (leftover from unrelated earlier "oracle
renaming" experimentation, `git log -- example-projects/hello-world-oracle-rename-new` shows commits
like "playing around with debugging oracle renaming", not anything prepared for this story) only
demonstrated **export**-side aliasing (`SmallComposition`'s adversary block renames `rand`'s
`UsefulOracle` to `ChangeNameUsefulOracle`/`AnotherUsefulOracle`); `Fwd`'s own import block was a
single unaliased `O(dummy) -> (Integer, Bits(n))`. Nothing in `src/` referenced this project before
this story (grepped), so it was free to extend.

Changed (all in `example-projects/hello-world-oracle-rename-new`):

- `packages/Fwd.pkg.ssp`: `import oracles` now declares two entries,
  `ChangeNameUsefulOracle`/`AnotherUsefulOracle`, both `(dummy: Integer) -> (Integer, Bits(n))`.
  `UsefulOracle`'s body calls both (`y <- invoke ChangeNameUsefulOracle(dummy); z <- invoke
  AnotherUsefulOracle(dummy); return z;`) so both import names appear in the translated proc, not
  just one.
- `games/MediumComposition.comp.ssp`, `MediumCompositionMoreOracles.comp.ssp`: `fwd`'s import block
  is now `{ ChangeNameUsefulOracle: UsefulOracle of rand, AnotherUsefulOracle: UsefulOracle of rand
  }` — one callee (`rand`), both edges aliased. Per §3.4's rule this is **not** eligible for direct
  pass (aliasing alone forces an adapter, independent of the single-callee shape) — a real,
  different-from-hello-world's-own-cases exercise of "aliased but single-callee ⇒ still an adapter".
  (§3.7's own text describes a *two-callee* case instead; a two-`Rand`-instance version was tried
  first and abandoned — see below — so this ended up simpler than the story's own illustration, but
  still a genuine, first-time-in-the-test-suite exercise of §3.3's import-name-vs-oracle-name
  distinction, which is the property the story's own §6 note flags as "the only place semantics can
  silently break".)
- `games/BigComposition.comp.ssp`: `fwd`'s block mirrors the above (both edges to `rand`, aliased);
  `fwd2`'s block is `{ ChangeNameUsefulOracle: UsefulOracle of fwd, AnotherUsefulOracle:
  UsefulOracle of fwd }` — same shape, callee `fwd` instead of `rand`.

**Deviation tried and reverted**: adding a second `rand2` instance (to get a genuine *two-callee*
adapter matching §3.7's literal text) broke the theorem's existing `reduction big_composition
medium_composition_more_oracles { map medium_composition big_composition { rand: rand, fwd: fwd
} }` — the reduction-mapping checker (`domino::code::theorem::reduction::mapping::*`) requires every
package instance of the mapped-from composition to appear in the map, and a second attempt (mapping
`rand2: rand2` after adding `rand2` to `BigComposition` too) hit
`reduction_inconsistent_assumption_boundary`, a reduction-hop invariant this story has no reason to
understand or touch. Reverted to the single-callee-but-aliased design above, which needs no change
to the reduction at all and still proves the point §3.3 exists to prove. `Proof` (the theorem) still
exports cleanly end to end (`domino easycrypt`, 10 files, one `Eq_*.ec` with the invariant's existing
`randomness: simple` claims untouched) — confirmed by hand and by the new tests in §4.

An earlier attempt at the oracle body used `parse invoke` tuple-pattern destructuring twice in one
oracle (`(a, _) <- parse invoke ...; (_, k) <- parse invoke ...; return (a, k);`) and hit what looks
like a real, **pre-existing, unrelated** bug: the second `Unwrap`-tuple-pattern assignment's target
identifiers were declared as locals (`collect_locals` correctly found them) but never actually
assigned in the translated body — likely a `treeify`/`unwrapify` interaction with two sequential
`Unwrap`-headed tuple patterns in one block. Not investigated further (out of this story's scope —
`package.rs`'s own invoke/pattern translation is unchanged by this story except the `module`/`proc`
resolution in §1.3, and this reproduces with a plain single-callee, non-aliased import too if
provoked the same way); worked around by using two plain single-identifier invokes instead
(§3.3's semantics don't need tuple patterns to be exercised). Flagged here rather than silently
worked around, per repo convention for a found-but-out-of-scope gap.

## 4. New tests

- `package.rs`: `hello_world_variant_names_collapse_fwd_and_fwd2` (replaces
  `hello_world_variant_names_show_fwd_fwd2_split`, name and assertion inverted:
  `vec!["Rand", "Fwd"]`, not `vec!["Rand", "Fwd_v1", "Fwd_v2"]`);
  `hello_world_fwd_and_fwd2_share_one_key_regardless_of_wiring` (replaces
  `hello_world_fwd_shares_a_key_across_compositions_but_not_with_fwd2`: the `assert_ne!` between
  `fwd`'s and `fwd2`'s keys is now `assert_eq!`); `distinct_int_param_literals_used_as_a_width_produce_distinct_variants`
  (renamed/re-targeted at a new `width_pkg` fixture whose `n` is a real `Bits` width, since the old
  `param_pkg` fixture's `n` was never a width and story 14 now drops exactly that kind of param from
  the key); `distinct_int_param_literals_not_used_as_a_width_still_produce_one_variant` (new — the
  direct acceptance test for §3.1's "non-width integer parameters ... don't distinguish variants").
- `interfaces.rs`: `no_module_type_in_interfaces_is_a_package_variant` (replaces the two deleted
  story-11 tests, §1.5 above).
- `game.rs`: `hello_world_no_composition_needs_an_adapter` (§3.4's "none in hello-world");
  `kem_dem_game_cca_dem_gets_exactly_one_adapter_for_dem` (§3.4's "one for `DEM` in kem-dem's
  `Game_CCA_DEM`" — asserts both the adapter count and its `implements: "Pkg_DEM.DEM_Imports"`);
  `hello_world_oracle_rename_new_medium_composition_gets_one_adapter_using_import_names` (§3.4's
  "one for `fwd`" bullet, and directly checks the adapter's two procs are named after the *import*
  names and both forward to `Pkg_Inst_Rand.d_UsefulOracle` — the *callee's* oracle name, proving
  §3.3 landed); `big_composition_has_two_instance_clones_of_the_fwd_package` rewritten to assert
  what's now literally true (one `Pkg_Fwd` variant, cloned as `Cloned_Pkg_Fwd`/`Cloned_Pkg_Fwd2`) in
  place of the old test's own correction-of-the-acceptance-text.
- `proof.rs`: no new tests needed — its existing golden/restriction tests already exercise the
  renamed paths (`restrictions_for`/`build_side_record_lit`) since `Simple4WHS`'s `Eq_*.ec` goldens
  are still checked, and the removal of `CompLayout.variant_names` has no externally-observable
  behavior beyond what those goldens already pin.

## 5. Which projects lost variants, and which instances got adapters vs. direct pass

| Project | Variants before → after | Detail |
|---|---|---|
| hello-world (`Proof`) | 3 → 2 | `Rand`, `Fwd_v1`, `Fwd_v2` → `Rand`, `Fwd`. The story's own headline example. |
| Simple4WHS | 7 → 7 | No change — its 7 variants (`Prot`/`KX`/`Prot_NoKey`/`KX_NoKeys`/`PRF`/`Prot_NoPrf`/`KX_NoPrf`) already differed by genuine `Bits`-width/`Fn` params or by being distinct packages, never by wiring alone. |
| kem-dem-cca-ssp | 9 → 8 | `KEM_v1`/`KEM_v2` → one `KEM` (confirmed by hand: `domino easycrypt`'s own `packages N variants (...)` summary line, run against both a pre-story-14 worktree and this one). |

| Composition | Instance | Direct pass or adapter |
|---|---|---|
| hello-world / every composition | every instance | direct pass (every edge unaliased, single-callee) — confirmed by `hello_world_no_composition_needs_an_adapter`. |
| kem-dem / `Game_CCA_DEM` (and `Game_MOD_CCA_PKE`, which also instantiates `DEM`) | `DEM` | adapter (`Pkg_Imports_DEM`, two callees: `Scheme_DEM` for `DEM_ENC`/`DEM_DEC`, `Key` for `GET`) — the story's own motivating multi-callee case. |
| kem-dem / `Game_MON_CCA_PKE` | `Scheme_PKE` | adapter (`Pkg_Imports_Scheme_PKE`). |
| kem-dem / `Game_MOD_CCA_PKE` | `KEM`, `MOD_CCA_PKE` | adapter each (`Pkg_Imports_KEM`, `Pkg_Imports_MOD_CCA_PKE`). |
| kem-dem / `Game_CCA_KEM` | `KEM` | adapter (`Pkg_Imports_KEM`). |
| hello-world-oracle-rename-new / `MediumComposition`, `MediumCompositionMoreOracles`, `BigComposition` | `fwd` (and, in `BigComposition`, `fwd2`) | adapter — single callee, but aliased (§3, deviated from the story's literal two-callee text; still a genuine adapter case). |

Stories 08/09 (named in this story's header as blocked on this one) should expect: an oracle-body
inline that crosses a package boundary via a direct pass is one hop (`Pkg_Inst_<callee>.d_X`); one
that crosses via an adapter is two (`Pkg_Imports_<inst>.d_Y` then `Pkg_Inst_<callee>.d_X` inside
it) — the table above is the per-composition, per-instance map of which is which, for every project
this repo currently has example projects for.

## 6. `CompLayout.variant_names` / `variant_name_map` — deleted, not kept

§7 asked this to be settled explicitly: **deleted outright**. `restrictions_for` and
`build_side_record_lit` only ever needed a variant's name to spell the pre-story-14
`Pkg_<inst>.<Variant>` path; post-story-14 every instance is `Pkg_Inst_<inst>` with no variant
component, so `compute_layout` no longer computes `variant_names` at all, and
`build_equivalence_file`/`compute_equivalence_files` no longer thread a `variant_name_map` parameter
through. Nothing else in `proof.rs` ever needed a variant's name at proof-writing time.

## 7. §2.1's EasyCrypt table, re-verified

Re-verified empirically, not just re-read: `easycrypt --version` reports `r2026.06-12-g7e192dd` on
this machine, matching the story's own "~r2026.06-era" expectation. Every one of the nine shapes in
the table is now exercised for real, not just checked once during the story's design, by the
existing test suite running with `easycrypt` on `PATH`:

- Rows 1–2 (`module type Imports`/`module Imports(O : Imports)` coexisting; an adapter ascribed to
  the uncloned type): every `Pkg_*.ec`/`Comp_*.ec` pair that has an adapter (§5's table) compiles as
  part of `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order`.
- Row 3 (extra procs on a direct-pass callee, width subtyping): `hello-world`'s `Fwd`/`Fwd2` passing
  `Pkg_Inst_Rand` (which also exposes `d_UselessOracle`, not in `Rand_Imports`... — there is no
  `Rand_Imports`, `Rand` has no imports; the real instance of this row is `KX_NoPrf`/`PRF` in
  Simple4WHS's `Hybrid2`, `Pkg_Inst_Prf` passed where the interface only needs `Eval`/`Hon` — `PRF`
  also exposes `NewKey`) via `simple_4whs_full_tree_compiles_in_dependency_order`.
- Rows 5–6 (alias / functor application denote the same memory cells): load-bearing for every
  `Eq_*.ec` that compiles today (`build_side_record_lit`'s `Pkg_Inst_<inst>.<field>{m}` reads) —
  `simple_4whs_full_tree_compiles_in_dependency_order` and
  `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` both compile every `Eq_*.ec` they produce.
- Row 7 (`declare module ... { -Pkg_Inst_m, -Pkg_Inst_n }`): every `Eq_*.ec`'s `declare module A`
  line, same tests.
- Row 8 (functor application two levels deep as another functor's argument):
  `hello-world`'s `BigComposition` — `Pkg_Inst_fwd2 = Cloned_Pkg_Fwd2.Fwd(Pkg_Inst_Fwd)` where
  `Pkg_Inst_Fwd` is itself `Cloned_Pkg_Fwd.Fwd(Pkg_Inst_Rand)` — via `hello_world_games_compile`.
- Row 9 (adapter calling into a functor application): kem-dem's `Pkg_Imports_KEM`/`Pkg_Imports_DEM`
  forwarding into `Pkg_Inst_*` instances that are themselves functor applications, via
  `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order`.

No shape needed correction; none of the nine were narrower or wider than the design assumed.

## 8. The Fn-params-as-init-arguments idea (§3.1, §7)

Not attempted, as instructed. It remains the last non-`Bits` reason a package can have several
variants: `Simple4WHS`'s `Prot`/`Prot_NoKey`/`Prot_NoPrf` and `KX`/`KX_NoKeys`/`KX_NoPrf` are, on
inspection, actually **distinct packages** (different `.pkg.ssp` files, not one package
parametrised), so `Simple4WHS`'s 7-variant count is not itself evidence either way for this idea;
`kem-dem-cca-ssp`'s `Scheme_DEM`/`Scheme_KEM`/`Scheme_PKE` similarly. No project in this repo
currently instantiates one `Fn`-parametrised package with two different function arguments, so this
story's changes don't produce a concrete before/after data point for it either — recorded here only
because §7 asked for it to be carried forward, not because anything new was learned about it.

## 9. Acceptance criteria, checked against what was actually built

- [x] `hello-world` exports **one** `Pkg_Fwd.ec` (no `_v1`/`_v2`), `module Fwd (O : Fwd_Imports)` —
      golden file, §5's table, `hello_world_variant_names_collapse_fwd_and_fwd2`.
- [x] No generated package file mentions `Interfaces`; no `Interfaces.ec` contains a `<Variant>_i`
      module type — grepped across every regenerated golden plus fresh `domino easycrypt` runs for
      kem-dem-cca-ssp and hello-world-oracle-rename-new (§ "verification run by hand" below);
      `no_module_type_in_interfaces_is_a_package_variant`.
- [x] Every instance in every `Comp_*.ec` is reachable as `Pkg_Inst_<inst>`; `Inst_` never appears
      without the `Pkg_` prefix; `Variant_` appears nowhere — grepped, see below (every hit is
      `Pkg_Inst_`, zero `Variant_` hits anywhere).
- [x] An adapter is emitted exactly when §3.4 says so: none in hello-world, one for `DEM` in
      kem-dem's `Game_CCA_DEM`, one for `fwd` in hello-world-oracle-rename-new's
      `MediumComposition` (deviated shape, §3 above; still a real adapter case) — §5's table, three
      new `game.rs` tests.
- [x] hello-world-oracle-rename-new exports: the package file's interface and body use the *import*
      names, the adapter maps them to the callee oracle names —
      `hello_world_oracle_rename_new_medium_composition_gets_one_adapter_using_import_names`
      asserts this directly (adapter procs `d_ChangeNameUsefulOracle`/`d_AnotherUsefulOracle`, both
      forwarding to `Pkg_Inst_Rand.d_UsefulOracle`).
- [x] `Eq_*.ec` restrictions and game-state record literals name `Comp_<X>.Pkg_Inst_<inst>.<field>`,
      no variant component — `proof.rs`'s existing golden/restriction tests, unchanged assertions,
      still pass against the new paths.
- [x] Every generated file still compiles with `easycrypt compile -I .` for Simple4WHS, Full4WHS and
      kem-dem-cca-ssp — the three `*_full_tree_compiles_in_dependency_order` tests, all green, no
      new failure beyond the two pre-existing gaps (story 07 §6.1/§6.2, reproduced identically,
      untouched by this story).
- [x] `CONTEXT.md`'s EasyCrypt section matches what is generated — it needed **no edit**: the
      glossary entries for *package variant*/*import interface*/*import adapter* (written when the
      design was settled, before this story's implementation) already describe exactly what §1
      above built; diffed by hand, zero discrepancies found.
- [x] Deterministic output (§2's bug found and fixed); `cargo build/test/clippy --workspace` clean.

## 10. Verification run by hand, end to end

```
cargo build --workspace
D=$PWD/target/debug/domino
```

- **hello-world**: still fails at *export* time on the pre-existing invariant-dialect gap (story 07
  §6.2, unrelated to and unaffected by this story) — verified via the targeted unit tests instead,
  per the story's own fallback instruction; §9's package/interface criteria all confirmed that way.
- **Simple4WHS**: `wrote _build/easycrypt/Simple4WHS (19 files)` — `packages 7 variants`, unchanged
  from before this story; `Interfaces.ec` has zero `<Variant>_i`/`{ include` occurrences (grep);
  every file compiles (`simple_4whs_full_tree_compiles_in_dependency_order`).
- **kem-dem-cca-ssp**: `wrote .../kem_dem_cca_ssp (16 files)` — `packages 8 variants` (was 9 on a
  pre-story-14 worktree, confirmed by hand, §5); `Game_CCA_DEM`'s `Comp_Game_CCA_DEM.ec` has exactly
  one `Pkg_Imports_DEM` module, ascribed to `Pkg_DEM.DEM_Imports`; every file compiles
  (`kem_dem_cca_ssp_full_tree_compiles_in_dependency_order`).
- **hello-world-oracle-rename-new** (`Proof`): `wrote .../Proof (10 files)` — no error, despite the
  package/composition edits in §3; grepped its output for `Variant_` (zero hits), `Interfaces` in
  any `Pkg_*.ec` (zero hits), bare `Inst_` without `Pkg_` prefix (zero hits).
- **Full4WHS**: covered by `full_4whs_full_tree_compiles_in_dependency_order`, green.
- Cross-project grep sweep (goldens plus fresh `domino easycrypt` output for kem-dem-cca-ssp and
  hello-world-oracle-rename-new, which aren't golden-tested): zero `Variant_` hits, zero bare
  `Inst_` hits, zero `Interfaces` references inside any `Pkg_*.ec`, zero non-`Iface_`/`Adv_` module
  types inside any `Interfaces.ec`.

## 11. State handed to the next story

- **`package::ordered_imports`** is the canonical, deterministic order for a package's imports —
  any later story (08/09) that needs to walk `pkg.imports` for rendering should use it, not
  `&pkg.imports` directly, for the reason in §2.
- **The parser-level nondeterminism in `Package::imports`'s own `Vec` order (§2) is still there** —
  this story worked around it in the writer layer; it was not fixed at the source. A future story
  touching the parser's import-block handling should know this workaround exists and either keep it
  or fix the root cause and remove it (searching for `ordered_imports` finds every call site).
- **Two-hop inlining**: stories 08/09 must handle an inlined oracle call passing through
  `Pkg_Imports_<inst>` first wherever §5's table says an adapter was used, and one hop everywhere
  else.
- **`hello-world-oracle-rename-new` is now a real, exercised fixture** for the import-alias/adapter
  path, not scratch content — a later story should not assume its shape is incidental.
