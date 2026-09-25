# Story 15 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (354 passed, 4 pre-existing
`#[ignore]`d, none failing) and `cargo clippy --workspace --all-targets` are clean. `easycrypt`
(`~/.opam/easycrypt/bin/easycrypt`, `r2026.06-12-g7e192dd`) was on `PATH`, so every compile-shaped
test ran for real, and the story's §5 recipe was run by hand on `Simple4WHS`, `Full4WHS` and
`kem-dem-cca-ssp`.

## 1. What changed

- `proof.rs`: `side_precondition_conjuncts` (per-parameter) is replaced by
  `side_precondition_conjunct(args, side, binder_mangled) -> Option<EcExpr>`, one conjunct per side:
  none for a zero-argument `run`, `arg{side} = <value>` for one argument (the bare value, not a
  one-tuple), `arg{side} = (<v1>, …, <vn>)` for more. It reuses `args_to_exprs`, so the values are
  the same mapping the `Pr[…]` arguments use. `build_byequiv_precondition` lost its two `Composition`
  parameters and its `Result`: with `run_param_names` gone nothing in it can fail.
- `proof.rs`: **`run_param_names` and its `debug_assert_eq!` are deleted**; nothing references them.
  No new AST node — `EcExpr::Qualified { path: ["arg"], mem }` and `EcExpr::Tuple` were enough.
- `names.rs`: new `RESERVED_NAMES: &[&str] = &["arg"]` (+ `is_reserved_name`), applied in the
  general (non-`Module`, non-`Lemma`) branch of `mangle_name` next to the keyword and `ec_` rules.
  A theorem constant `arg` now mangles to `d_arg`. It is a separate list rather than an entry in
  `KEYWORDS` because `KEYWORDS` is documented as `ecLexer.mll`'s reserved words and `arg` is not
  one; both lists have a `*_are_sorted` test. Lemma names are left alone — a lemma called `arg`
  shadows nothing.
- `mod.rs::test_support`: `assert_compiles_with_paths` and `assert_compiles_or_known_base_case_gap`
  now share `run_compile` and both call `assert_no_unused_memory_warning`, which fails on
  `unused memory` in stdout/stderr. The tolerance helper still tolerates a base-case failure, but
  not that warning, even in a file that fails for the known reason. Its doc comment lists what
  genuinely still needs it.
- Binders are **not** renamed (§3.3); they stay spelled after the Domino theorem constant.

## 2. Rendered preconditions

All three shapes below were read from the generated files (`domino easycrypt --theorem …`), and each
`Eq_*.ec` was compiled with `easycrypt compile -I .`. **No file produced an `unused memory` line.**

### `Simple4WHS`

| File | Precondition (after `={glob A}`) | Compiles |
|---|---|---|
| `Eq_Hybrid0_Hybrid1.ec` | `arg{1} = b` `/\ arg{2} = b` | clean |
| `Eq_Hybrid1_Hybrid2.ec` | `arg{1} = b` `/\ arg{2} = (b, false)` | clean |
| `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` | `arg{1} = (false, true)` `/\ arg{2} = (true, true)` | clean |

### `Full4WHS`

| File | Precondition (after `={glob A}`) | Compiles |
|---|---|---|
| `Eq_H0_H1_0.ec` | `arg{1} = b` `/\ arg{2} = (b, false)` | **base case fails** |
| `Eq_H1_1_H2_0.ec` | `arg{1} = (b, true)` `/\ arg{2} = (b, false)` | **base case fails** |
| `Eq_H2_1_H3_0.ec` | `arg{1} = (b, true)` `/\ arg{2} = (b, true)` | clean |
| `Eq_H3_1_H4.ec` | `arg{1} = (b, false)` `/\ arg{2} = b` | **base case fails** |
| `Eq_H4_H5.ec` | `arg{1} = b` `/\ arg{2} = b` | clean |
| `Eq_H5_H6_0.ec` | `arg{1} = b` `/\ arg{2} = (b, false, b)` | clean |
| `Eq_H6_1_0_H6_1_1.ec` | `arg{1} = (b, true, false)` `/\ arg{2} = (b, true, true)` | clean |
| `Eq_H6_1_1_H7_0.ec` | `arg{1} = (b, true, true)` `/\ arg{2} = (b, false, true)` | clean |
| `Eq_H7_1_1_0_H7_1_1_1.ec` | `arg{1} = (false, true, true)` `/\ arg{2} = (true, true, true)` | clean |

### `kem-dem-cca-ssp`

`Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.ec`: `arg{1} = b` `/\ arg{2} = (b, false)`. Fails at
the base case only (`cannot prove goal (strict)`, line 22). Unchanged in kind from story 13.

## 3. Files moved off the tolerance helper

The story expected one (`Eq_H4_H5.ec`). Four moved to plain `assert_compiles`:

- `Simple4WHS`: **`Eq_Hybrid0_Hybrid1.ec`, `Eq_Hybrid1_Hybrid2.ec`** — the whole `Simple4WHS` loop in
  `export.rs` is now plain `assert_compiles`, with no per-file branch left.
- `Full4WHS`: **`Eq_H2_1_H3_0.ec`, `Eq_H4_H5.ec`**.

`full_4whs_full_tree_compiles_in_dependency_order` now has an explicit `KNOWN_BASE_CASE_GAPS` list
of three files and uses plain `assert_compiles` for the other six. `kem_dem_cca_ssp_…` is unchanged
and still tolerant.

**Still needing `assert_compiles_or_known_base_case_gap`** (base case only, identical failure mode):
`Eq_H0_H1_0.ec`, `Eq_H1_1_H2_0.ec`, `Eq_H3_1_H4.ec` (`Full4WHS`) and `kem-dem-cca-ssp`'s one hop.
`Eq_H0_H1_0.ec` is the story's acceptance case: it renders `arg{1} = b` / `arg{2} = (b, false)`,
the `unused memory` warning is gone, and its remaining failure is the base case only — story 13
§1.1's already-recorded state-record gap, not chased here.

## 4. Acceptance criteria

- [x] No generated `Eq_*.ec` compiles with an `unused memory` warning; the compile helpers now
      *fail* on that text (`assert_no_unused_memory_warning`), and the by-hand run found none.
- [x] `Eq_H4_H5.ec` compiles with plain `assert_compiles`, base case discharged.
- [x] `Eq_H0_H1_0.ec` renders `arg{1} = b` and `arg{2} = (b, false)`
      (`full_4whs_h0_h1_0_precondition_has_different_arities_per_side`); its remaining failure is
      the base case only.
- [x] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` compiles clean as `arg{1} = (false, true)` /
      `arg{2} = (true, true)`.
- [x] One-argument sides render `arg{n} = <value>`, not `arg{n} = (<value>)`
      (`hybrid0_hybrid1_precondition_lists_both_sides_of_the_shared_binder`).
- [x] A theorem constant named `arg` mangles to `d_arg` (`mangle_arg_is_escaped`).
- [x] `run_param_names` is deleted; nothing references it.
- [x] Deterministic (`rendering_is_deterministic` unchanged); build/test/clippy clean.

New tests beyond the criteria: `hybrid1_hybrid2_precondition_has_a_tuple_on_the_side_with_two_arguments`,
`no_precondition_names_a_run_parameter_directly` (every conjunct on `Simple4WHS` and `Full4WHS` goes
through `arg`), `a_side_with_no_run_arguments_contributes_no_conjunct` (0-arity omission, on
`build_byequiv_precondition` directly — no project in the repo has a zero-argument `run`, so the
`(: ={glob A} ==> _)` shape is unit-tested, not compiled), and `reserved_names_are_sorted`.

## 5. State handed to the next story

- The precondition is `={glob A}` plus at most one `arg{side} = …` per side. Nothing outside
  `proof.rs` builds it.
- **Story 13's diagnosis of the residual gap was partly wrong.** It attributed the `Simple4WHS`
  cross-composition failures to `params_inv` losing the tie to `&m`. Those two hops
  (`Eq_Hybrid0_Hybrid1`, `Eq_Hybrid1_Hybrid2`) and two `Full4WHS` ones (`Eq_H2_1_H3_0`, `Eq_H4_H5`)
  in fact failed because the old precondition was silently voided by the binder-shadowing bug. Only
  three `Full4WHS` hops plus `kem-dem-cca-ssp` remain; anyone chasing the base-case gap should
  start from those and not from story 13's §2.1 goal excerpts.
- `assert_no_unused_memory_warning` is applied to every `Eq_*.ec`, `Pkg_*.ec`, `Comp_*.ec` and
  `*_Invariants.ec` compile, since all go through the shared helpers — it also guards any future
  relational formula.

## 6. Notes for follow-up

- `domino easycrypt` on `example-projects/hello-world` still fails at export with
  `unsupported SMT sort <GameState_MediumComposition_<$<!n!>$>>` from `theorem/invariant.smt2` —
  an invariant-translation problem (story 07 §6.2), unrelated and untouched.
- Whether `arg` should also be reserved for `NameKind::Lemma`/`Module` was considered and left
  out: neither can shadow a program identifier in a formula.


---

## Corrected by story 19

The "known base-case gap" diagnosis above (the `smt(emptyE map_empty)` failing for want of a tie
between the two sides' `run` arguments) was wrong. `auto => />.` already closes the base case, so
the following `smt` ran on the first oracle's goal. Story 19 emits `auto => />; smt(emptyE
map_empty).` as one line; every file this report lists as needing the helper now compiles, and the tolerance
helper is gone.
