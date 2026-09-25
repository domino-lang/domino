# Story 13 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (345 passed, 4 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`~/.opam/easycrypt/bin/easycrypt`, `r2026.06-12-g7e192dd`, resolved via the developer's
opam switch) was on `PATH`, so every compile-shaped test ran for real, plus the story's own §5
recipe (and its natural extension to `Full4WHS` and `kem-dem-cca-ssp`) was run by hand, end to end.

## 1. What changed

### 1.1 The `byequiv` relational precondition (§3.1, §3.2)

- `ast.rs`: `ProofLine` changed from a struct to an enum: `ProofLine::Tactic { indent, bullet, text
  }` (byte-identical behavior to the old struct, just renamed) and a new `ProofLine::
  ByequivPrecondition { conjuncts: Vec<EcExpr> }`, which carries the induction start's own
  relational precondition as real structured data rather than pre-joined text with embedded
  newlines. `EcExpr` gained `GlobEq(String)` for `={glob M}` — the one primitive EasyCrypt formula
  shape (glob-variable equality between the two runs) that didn't already have an AST node; atom
  precedence, like every other self-delimited literal in that enum.
- `render.rs`: `render_proof_line` matches on the new `ProofLine` enum; a new
  `render_byequiv_precondition` renders `conjuncts` as `byequiv\n  (: <c0>\n     /\ <c1>\n     ...\n
  ==> _) => //.` — one conjunct per line, `={glob A}` always first, exactly the shape in the story's
  own worked example. `render_expr_inner`/`prec` gained the `GlobEq` case (`={glob M}`, atom
  precedence).
- `proof.rs`:
  - `run_param_names(comp)` reproduces `game.rs::render_game_file`'s own `init_args` naming (a fresh
    `Names(Var)` over the exact same `composition_const_needs_arg` filter) independently, so it is
    always the same length, same order, same spelling as `Exp_<mangled>.run`'s actual parameter list
    — and, by construction, the same length and order as `side_run_args`'s own result for the same
    composition (both filter `comp.consts` identically).
  - `side_precondition_conjuncts(comp, args, side, binder_mangled)` zips `run_param_names(comp)`
    with that side's already-resolved `RunArgValue`s and emits one `<param>{side} = <value>`
    conjunct per parameter — a literal renders verbatim, a theorem-constant reference renders as
    that constant's mangled lemma binder. Every parameter is listed unconditionally (no dedup
    against the other side).
  - `build_byequiv_precondition(...)` assembles `[GlobEq("A")] ++ side_1_conjuncts ++
    side_2_conjuncts`.
  - `build_equivalence_file` now builds this precondition right after resolving `left_args`/
    `right_args`/`binder_mangled` (already computed for the `Pr[...]` arguments and lemma binders)
    and pushes it as the *first* proof line, replacing the old bare `plain_line("byequiv => //.")`.
- `tests.rs` (story01's kitchen-sink golden fixture): updated its `ProofLine { ... }` literals to
  `ProofLine::Tactic { ... }` — no change to the rendered golden text, since `Tactic`'s fields and
  rendering are unchanged.

### 1.2 The duplicate `qed.` (§3.3)

Deleted the `proof.push(plain_line("qed."));` that used to follow the oracle-bullet loop in
`build_equivalence_file` (current line ~560, was `proof.rs:457` before story 10 shifted line
numbers). `render_lemma` (`render.rs:374`, `out.push_str("qed.")`) is now the sole owner of the
closing `qed.`. New regression test `every_generated_lemma_has_exactly_one_qed` renders all three of
`Simple4WHS`'s `Eq_*.ec` files and asserts `rendered.matches("qed.").count() == 1` for each.

### 1.3 The base-case tolerance helper, narrowed (§3.4)

`mod.rs::test_support::assert_compiles_or_known_base_case_gap`'s doc comment is rewritten to record
what was actually found by compiling every target project's output for real (§2 below), rather than
restating story 07's original blanket claim. It is **not** deleted — it still has real callers
(§2.4) — but its scope is now accurately "still needed for these specific files", not "needed for
every `Eq_*.ec`".

`export.rs::simple_4whs_full_tree_compiles_in_dependency_order` now special-cases
`Eq_Real_Hybrid3_Ideal_Hybrid3.ec`: plain `assert_compiles` (no tolerance), while
`Eq_Hybrid0_Hybrid1.ec` and `Eq_Hybrid1_Hybrid2.ec` still go through
`assert_compiles_or_known_base_case_gap`. `full_4whs_full_tree_compiles_in_dependency_order` and
`kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` are **unchanged** — both already call
`assert_compiles_or_known_base_case_gap` for every equivalence's proof file, and that helper accepts
a clean compile too (it only special-cases the *known failure*, `output.status.success()` returns
immediately), so it stays correct for both the hops that now discharge cleanly and the ones that
still don't, without needing per-hop branching in those two tests. Splitting `Simple4WHS`'s test was
necessary only because its acceptance criterion specifically demands **no tolerance at all** for
`Eq_Real_Hybrid3_Ideal_Hybrid3.ec` — a plain `assert_compiles` failure is a hard test failure, so
that file needed to be pulled out of the loop.

## 2. Verified against real `easycrypt`, every target project

### 2.1 `Simple4WHS` — the story's own acceptance target

Rendered preconditions (`domino easycrypt --theorem Simple4WHS`, then read the generated files):

```
Eq_Real_Hybrid3_Ideal_Hybrid3.ec:
byequiv
  (: ={glob A}
     /\ b{1} = false
     /\ bprf{1} = true
     /\ b{2} = true
     /\ bprf{2} = true
     ==> _) => //.

Eq_Hybrid0_Hybrid1.ec:
byequiv
  (: ={glob A}
     /\ b{1} = b
     /\ b{2} = b
     ==> _) => //.

Eq_Hybrid1_Hybrid2.ec:
byequiv
  (: ={glob A}
     /\ b{1} = b
     /\ b{2} = b
     /\ bprf{2} = false
     ==> _) => //.
```

Exactly the story's own worked example for the first, and exactly the acceptance criterion's own
`b{1} = b /\ b{2} = b` (both sides of the shared binder listed, never `={b}`) for the second.

`easycrypt compile -I . <file>.ec` for all 19 files, in dependency order:

- **`Eq_Real_Hybrid3_Ideal_Hybrid3.ec` compiles clean, exit 0** — the acceptance bar. Only benign
  `[warning]`s (uninitialized-local-variable warnings on oracle procs that are never actually read
  before written on the abort path — pre-existing, unrelated to this story). This is a **real base
  case discharge**: the base case is a *same-composition* hop (`Comp_Hybrid2` on both sides,
  differing only in the two `run` literals), so the precondition's `b{1} = false /\ bprf{1} = true /\
  b{2} = true /\ bprf{2} = true` is exactly the fact `params_inv`'s post-generalization `forall &1
  &2` step needed and previously had no way to state.
- **`Eq_Hybrid0_Hybrid1.ec` and `Eq_Hybrid1_Hybrid2.ec` still fail, only at the base case**
  (`[critical] cannot prove goal (strict)` at the exact `smt(emptyE map_empty).` line — line 22 and
  23 respectively, i.e. the very next line after the rendered precondition/`call`/`auto`). Every
  earlier line (`Types.ec`, `Interfaces.ec`, every `Variant_*.ec`/`Comp_*.ec`, both
  `Eq_*_Invariants.ec`, the `declare module`, the lemma statement, `proc; inline.`, `call (: inv
  …); last first.`, `auto => />.`) type-checks. `easycrypt llm -lastgoals` on both shows the same
  residual shape: after `call`'s own `last first` reordering and `auto => />`, the base-case goal is
  universally quantified over fresh memories (`forall &1 &2, params_inv {...} {...} /\
  Domino_state_eq ... /\ ...`), and inside that quantified body the composition-const value that the
  top-level precondition tied to a fixed `&m` is now printed as two *different*, unrelated-looking
  atoms — `l_pkg_KX_b = b{!1}` on the left record literal and `r_pkg_KX_b = b{!2}` on the right —
  because `Hybrid0`'s `KX` and `Hybrid1`'s `KX_NoKeys` are genuinely different modules with
  genuinely different state shapes (`Hybrid0`'s left record has 11 fields including `d_First`/
  `d_Second`; `Hybrid1`'s right record has 9, without them). `smt(emptyE map_empty)` — and even bare
  `smt()` — cannot re-derive `b{!1} = b{!2}` from nothing once the induction has generalized away the
  fixed memory the precondition constrained. This is the exact gap the story's own §1.1 predicted
  and told this session not to chase by widening the `smt` call. Representative excerpt (from
  `Eq_Hybrid0_Hybrid1.ec`'s own `easycrypt llm -lastgoals` output, `Current goal (remaining: 10)`):

  ```
  forall &1 &2,
    params_inv
      {| ...; l_pkg_KX_b = b{!1}; l_abort_flag = false; |}
      {| ...; r_pkg_KX_b = b{!2}; r_abort_flag = false; |} /\
    Domino_state_eq ... /\ Domino_keys_computed_correctly ... /\ Domino_time_of_acceptance ...
  ```

  Byte-identical failure mode (same predicate shape, same `b{!1}`/`b{!2}` split, same tactic
  position) for `Eq_Hybrid1_Hybrid2.ec`.

### 2.2 `Full4WHS` — beyond the story's own named targets, tried anyway (same session, no extra scope)

`domino easycrypt --theorem Full4WHS` (50 files, 9 equivalence hops) — every prerequisite file
(`Types.ec`, `Interfaces.ec`, all 18 `Variant_*.ec`, all 12 `Comp_*.ec`, all 9
`Eq_*_Invariants.ec`) compiles clean, as before. Compiling all nine `Eq_*.ec` files individually:

| File | Result |
|---|---|
| `Eq_H0_H1_0.ec` | fails, base case only (`cannot prove goal (strict)`, line 23) |
| `Eq_H1_1_H2_0.ec` | fails, base case only (line 24) |
| `Eq_H2_1_H3_0.ec` | fails, base case only (line 24) |
| `Eq_H3_1_H4.ec` | fails, base case only (line 23) |
| `Eq_H4_H5.ec` | fails, base case only (line 22) |
| `Eq_H5_H6_0.ec` | **compiles clean** |
| `Eq_H6_1_0_H6_1_1.ec` | **compiles clean** |
| `Eq_H6_1_1_H7_0.ec` | **compiles clean** |
| `Eq_H7_1_1_0_H7_1_1_1.ec` | **compiles clean** |

Every failure is the identical, single known gap (`smt(emptyE map_empty)` at the exact next line
after the precondition/`call`/`auto`) — no new or different failure mode anywhere. **This is not a
clean "same-composition passes, cross-composition fails" split**: `Eq_H6_1_0_H6_1_1.ec` and
`Eq_H7_1_1_0_H7_1_1_1.ec` are same-composition hops (`require Comp_H6.` / `require Comp_H7.` — one
name) and compile clean, as expected from §2.1's reasoning; but `Eq_H5_H6_0.ec` is a genuine
**cross**-composition hop (`require Comp_H5 Comp_H6.` — `Game_H5`'s `KX_nokey` vs. `Game_H6`'s
`KX_noprfkey_v1`, structurally different records, same as the failing hops) and it *still* compiles
clean. Investigating exactly which invariant shape makes a cross-composition hop's base case
discharge vs. not is outside this story's scope (§3.4/§6 both say record the goal, don't chase it) —
flagged under §5 "Notes for follow-up" instead of investigated further.

### 2.3 `kem-dem-cca-ssp`

`domino easycrypt --theorem kem_dem_cca_ssp` (17 files, its one equivalence hop,
`Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.ec`, a cross-composition hop — `Game_MON_CCA_PKE` vs.
`Game_MOD_CCA_PKE`). Precondition: `={glob A} /\ b{1} = b /\ dem_idealization{2} = b /\
key_idealization{2} = false`. Compiles up through the `call`/`auto`, fails only at the base case
(`smt(emptyE map_empty)`, line 23, `cannot prove goal (strict)`) — same known gap, no regression.
Still needs `assert_compiles_or_known_base_case_gap` (which it already had, unchanged).

### 2.4 `hello-world`

Still fails at **export** time with the exact same pre-existing, out-of-scope error stories 07/10/
11/12 already documented (`unsupported SMT sort <GameState_MediumComposition_...>` —
`hello-world`'s hand-written invariant predates story 06's grammar entirely). Verified by hand
(byte-identical error text to before this story). This story's own change is entirely downstream of
invariant translation, so it cannot affect this gap either way; verified instead via
`proof.rs`'s/`export.rs`'s own unit and compile-shaped tests, same as stories 11/12 did.

## 3. Acceptance criteria, checked against what was actually built

- [x] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` compiles with **`assert_compiles`**, no tolerance — verified
      both by hand (`easycrypt compile -I . Eq_Real_Hybrid3_Ideal_Hybrid3.ec`, exit 0) and by
      `export.rs::simple_4whs_full_tree_compiles_in_dependency_order`, which now calls plain
      `assert_compiles` for exactly this file.
- [x] Its `byequiv` reads exactly the shape in §1 of the story (`={glob A} /\ b{1} = false /\
      bprf{1} = true /\ b{2} = true /\ bprf{2} = true ==> _) => //.`), confirmed both by reading the
      generated file (§2.1) and by the new unit test
      `real_hybrid3_ideal_hybrid3_precondition_lists_every_literal_on_both_sides`.
- [x] `Eq_Hybrid0_Hybrid1.ec` renders `b{1} = b /\ b{2} = b` (same binder, both sides listed) —
      confirmed by reading the generated file and by the new unit test
      `hybrid0_hybrid1_precondition_lists_both_sides_of_the_shared_binder`.
- [x] Exactly one `qed.` per lemma in every generated `Eq_*.ec` — confirmed by `grep -c "^qed\.$"`
      on all three `Simple4WHS` files (each `1`) and by the new unit test
      `every_generated_lemma_has_exactly_one_qed`.
- [x] The two cross-composition hops named by the story (`Eq_Hybrid0_Hybrid1.ec`,
      `Eq_Hybrid1_Hybrid2.ec`) still export and still fail only at the base case; the failing goal
      is recorded verbatim in §2.1 above (and, more fully, was captured via `easycrypt llm
      -lastgoals`).
- [x] `hello-world` and `kem-dem-cca-ssp` `Eq_*.ec` files still compile (`kem-dem-cca-ssp`'s, up to
      and including the same known base-case gap it already had, §2.3; `hello-world` still fails at
      export for its own unrelated, pre-existing reason, §2.4 — nothing about this story changes
      either outcome).
- [x] Deterministic (`proof::tests::rendering_is_deterministic`, unchanged, still passes);
      `cargo build/test/clippy --workspace` clean.

## 4. State handed to the next story

- **`ProofLine` is now an enum**, not a struct: `ProofLine::Tactic { indent, bullet, text }` (old
  behavior, renamed) and `ProofLine::ByequivPrecondition { conjuncts: Vec<EcExpr> }` (new). Any
  future code building a `Vec<ProofLine>` by hand (tests, a future story) must match this shape.
  `EcExpr` gained one new variant, `GlobEq(String)` (`={glob M}`) — every `match e { ... }` over
  `EcExpr` in the crate needed (and now has) an arm for it; `invariant.rs::expr_references_var`
  needed the one real code update (`GlobEq` never references a local variable, so `=> false`).
- **`run_param_names(comp)`** (`proof.rs`) is a new, independently-useful helper: the exact mangled
  parameter-name list `Exp_<mangled>.run` uses, in `comp.consts` order. A future story needing to
  build another formula over a composition's own `run` arguments (by name, not just by resolved
  value) can reuse it rather than re-deriving `game.rs`'s `init_args` naming a third time.
- **The residual base-case gap is not simply "same composition vs. cross composition"** — §2.2's
  `Eq_H5_H6_0.ec` finding is worth remembering before a future session assumes that rule and tries
  to "fix" the remaining five `Full4WHS` hops (or `Eq_Hybrid0_Hybrid1.ec`/`Eq_Hybrid1_Hybrid2.ec`/
  `kem-dem-cca-ssp`'s hop) by further generalizing the precondition. The actual discriminator looks
  to be something in each hop's own `params_inv`/state-relation content (whether it happens to pin
  down enough of the two sides' state that the induction step's `forall &1 &2` doesn't need the
  now-lost tie to `&m` at all) — investigating that is a `params_inv`/story-06-shaped follow-up, not
  a `byequiv`-shaped one.
- **`assert_compiles_or_known_base_case_gap` still has real callers**: `export.rs`'s
  `simple_4whs_full_tree_compiles_in_dependency_order` (for `Eq_Hybrid0_Hybrid1.ec`/
  `Eq_Hybrid1_Hybrid2.ec` only now), `full_4whs_full_tree_compiles_in_dependency_order` and
  `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` (unchanged, every equivalence in the
  loop — correct because the helper tolerates a clean compile too). It is not obsolete and should
  not be deleted.

## 5. Notes for follow-up (not this story's scope)

- Story 07's §6.2 `GameState_`-dialect gap (`hello-world`/`simple-KEM-example`) is exactly as
  documented before — untouched, unaffected.
- The `Eq_H5_H6_0.ec` finding in §2.2/§4 — a cross-composition hop whose base case already
  discharges — is worth a future session's attention if someone wants to close the remaining five
  `Full4WHS` gaps, `Simple4WHS`'s two, or `kem-dem-cca-ssp`'s one: diffing `Eq_H5_H6_0_Invariants.ec`
  against, say, `Eq_H0_H1_0_Invariants.ec` to see what's different about their `params_inv`/
  `Domino_*` predicates would be the natural next step, not attempted here per the story's own
  explicit instruction not to chase this.


---

## Corrected by story 19

The "known base-case gap" diagnosis above (the `smt(emptyE map_empty)` failing for want of a tie
between the two sides' `run` arguments) was wrong. `auto => />.` already closes the base case, so
the following `smt` ran on the first oracle's goal. Story 19 emits `auto => />; smt(emptyE
map_empty).` as one line; every file this report calls tolerated now compiles, and the tolerance
helper is gone.
