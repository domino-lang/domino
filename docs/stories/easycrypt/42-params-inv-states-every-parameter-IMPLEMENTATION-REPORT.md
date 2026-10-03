# Story 42 — implementation report

## What changed

- **`src/writers/easycrypt/invariant.rs`**
  - §3.1: one record type `<Pkg>_pkgstate` per package with state that an instance on either side
    uses. Fields are `<Pkg>_<mangled field>` (`KX_d_LTK`), mangled through one `Names` per instance,
    as the package's own module variables are. The types come first in the file, in order of first
    use (left side, then right side, `ordered_pkgs_idx()` order). Two instances of one package whose
    fields translate to different types are a hard `InvariantError::PackageStateMismatch`.
  - §3.2: `build_side_record` builds the new game record: `{l_|r_}pkg_<Inst> : <Pkg>_pkgstate` per
    instance with state, then `{l_|r_}pkg_<Inst>_<param>` per `param_needs_var` parameter, both in
    `ordered_pkgs_idx()` order, then `{l_|r_}abort_flag`. The naming rule is five `pub(super)`
    helpers (`pkg_state_type_name`, `pkg_state_field_name`, `instance_field_name`,
    `param_field_name`, `abort_field_name`), shared with `proof.rs`.
  - §3.3: the lookup is now `StateLookup { fields, instances }`.
    - `fields` maps `{left|right}.<Inst>.<raw name>` to the projection: a state field reads
      ``l.`l_pkg_KX.`KX_d_State``, a parameter ``l.`l_pkg_KX_b``.
    - `instances` maps `{left|right}.<Inst>` to an `InstanceEntry { package, state }`.
    - `translate_instance_equality` uses it. Same package with state gives one record equality,
      same package without state gives `true`, and different packages give a hard
      `InvariantError::PackageMismatch` naming both instances and packages. Parameters never take
      part. Its doc comment no longer mentions `build_params_inv`.
  - §3.1 collisions: `check_unique_fields` makes two fields with one name, across every
    `<Pkg>_pkgstate` and both game records, a hard `InvariantError::FieldCollision`. `Names` is per
    instance and the field names join package, instance and parameter names with `_`, so for
    example instance `T_b1` and parameter `b1` of instance `T` both give `l_pkg_T_b1`.
  - §3.4: `build_params_inv(left, right)` follows the binding rule. Each side record carries its
    `ParamField`s (instance, parameter, projection, binding) in record order. Literals are pinned,
    and each later field bound to a theorem constant is equated with the previous one. The only
    field bound to a constant contributes nothing. An unresolvable binding is a hard
    `InvariantError::UnresolvedParam`. No real project trips it.
- **`src/writers/easycrypt/proof.rs`** (§3.5): `build_side_record_lit` builds the nested literal:
  `l_pkg_KX = {| KX_d_LTK = Comp_H1.Pkg_Inst_KX.d_LTK{1}; … |}`, then the parameter fields, then
  `l_abort_flag`. It uses the shared naming helpers, and story 43's `render_record_block` lays it
  out with no new layout code.
- **Docs**:
  - `CONTEXT.md`: the *Game-state record* entry describes the nested record (ADR 0007).
  - `06-invariant-translation-IMPLEMENTATION-REPORT.md` §7 and §11 have the dated note (§3.6).
  - The overview §3 "Game-state record" row is marked *Amended by story 42*.
- **Test project** `testdata/easycrypt/story42/params/` has packages `Ctr`, `CtrToo`, `Pass` (no
  state), `Twin` and `Key`, compositions `Left`, `Right`, `Narrow`, `Wide` and `Clash`, and four theorems:
  - `Params`: `L ~ R`. All cases, and the theorem exports and compiles as a whole.
  - `ParamsBad`: `L_bad ~ R_bad`. A whole-package equality between `Ctr` and `CtrToo`.
  - `ParamsWidths`: `N ~ W`. Package `Key` with state `Bits(n)`, with `n` bound to different
    theorem constants.
  - `ParamsClash`: `C1 ~ C2`, both `Clash`, where instance `T_b1` and parameter `b1` of instance
    `T` both name `l_pkg_T_b1`.

  The table at the top of the tests in `invariant.rs` lists every binding.
- **Goldens**:
  - New: `testdata/easycrypt/story42/4WHS/Eq_H1_1_H2_0_Invariants.ec` (Full4WHS).
  - Regenerated: `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`.
  - No golden contains `call (: inv`. The call is pinned by `proof.rs` tests.

## Verification

Final runs, after the review fixes, with `DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`:

| Binary | `cargo test --workspace` | `--features cvc5-lib` |
|---|---|---|
| lib (`sspverif`) | 582 passed, 5 ignored | 670 passed, 6 ignored |
| `debug_all_claims` | 3 | 4 |
| `easycrypt_ctrl_c` | 0 | 4 |
| `easycrypt_lockstep_progress` | 0 | 1 |
| `easycrypt_overwrite` | 6 | 6 |
| `easycrypt_progress` | 1 | 1 |
| `easycrypt_prove` | 0 | 5 |
| `easycrypt_tactics_writes` | 0 | 3 |
| `sspverif_smtlib` | 2 | 2 |

There were no failures in either run. `cargo test --lib writers::easycrypt` passes 275 tests.

`cargo clippy --workspace --all-targets` (both feature sets) reports only the warnings that predate this
story: `src/debug/sweep.rs:199`, plus the `TempDir::into_path` deprecations with `cvc5-lib`.

Checks against real exports (baseline binary built from e0234014):

- Simple4WHS and Full4WHS: every file outside `Eq_*` is byte-identical to the baseline.
- All 32 `Eq_*.ec` / `Eq_*_Invariants.ec` files compile with `easycrypt compile`, and so do the
  `Params` theorem's `Eq_L_R.ec` and `Eq_L_R_Invariants.ec`.
- `check-alignment` on Simple4WHS: "27 oracles checked, 0 mismatches".
- Every Full4WHS row of §1.1 appears in the regenerated `params_inv`. The one exception is
  `H0 ~ H1_0`; see below.
- No `Domino_` operator equates a parameter field.
- The completeness test (§4.2) was mutation-checked: dropping the `CR.b` pin makes it fail.

## Deviations and notes

- **The story's §1.1 table is wrong for `H0 ~ H1_0`.** It says `r.Nonces.b = true`. `H1_0` binds
  `bnonce: false`, and `H1` passes `b: bnonce` to `Nonces`, so the regenerated `params_inv` says
  ``r.`r_pkg_Nonces_b = false``. Every other row is present as the table states it.
- **Field order in the game record.** §3.2 lists the instance fields, then the parameters, then
  `abort_flag`, and ADR 0007 says "one field of that type per instance with state, then one field
  per parameter". I read that as all package records first, then all parameters, not interleaved
  per instance. `params_inv`'s conjunct order is the parameters' record order (§3.4).
- **`PackageStateMismatch` and `UnresolvedParam` were not asked to have tests in §4.**
  `PackageStateMismatch` has one through `ParamsWidths`. `UnresolvedParam` has none: it needs a parameter
  bound to an expression that is neither a literal nor a bare constant, and no project in the
  repository has one. Story 06's comments say there is none. The completeness test resolves every
  parameter of every 4WHS equivalence.
- **A whole-instance atom outside a two-argument `=`** (for example passed to a function) stays an
  unrecognised atom, as before. The story only asks for the equality.
- **Package names are not mangled** in `<Pkg>_pkgstate` or the `<Pkg>_` field prefix, just as
  instance names are not mangled in `l_pkg_<Inst>`. EasyCrypt accepts uppercase-first type and
  record field names (compiled).
- **Owner-run checks (§5), left unchecked:**
  - [ ] `Simple4WHS` `prove -f` has no more admits than before.
  - [ ] `Full4WHS` `H1_1 ~ H2_0` has 0 `J1 side-goal` admits.

  `prove` was not run on 4WHS (overview §7). §7's risk applies: after `rewrite /inv`, smt has to
  see through two levels of record literal.

## Code review

The `code-review` skill ran against e0234014 with two sub-agents. The spec was the story file and
ADR 0007, since the commits reference no issue. `docs/agents/issue-tracker.md` is missing (the
skill suggests `/setup-matt-pocock-skills`).

**Standards** (3 documented-standard findings, 5 smells):

- *No implementation report*: it existed, untracked; the reviewer missed it. No change.
- *`CONTEXT.md` still says the record is flat*: fixed.
- *Names can collide across packages and instances, against §3.1*: fixed with
  `FieldCollision` and the `ParamsClash` test. A mutation check (the check removed) makes the test
  fail.
- *Primitive Obsession* (the instance name parsed back out of the lookup key): fixed;
  `InstanceEntry` carries `instance`.
- *A wildcard where a hard error is expected* in `translate_instance_equality`: fixed;
  `(None, None)` is matched and the impossible mixed case is `unreachable!`.
- *`abort_flag` field name written twice*: fixed with `abort_field_name`.
- *Duplicated code between the two record builders*, *the `(binder, op_param, prefix)` data
  clump*, and *record-layout naming living in `invariant.rs`*: not done; recorded under
  follow-up as one refactor.

**Spec** (no substantive defects):

- *§3.1 collision guarantee not met*: fixed (same fix as above).
- *`UnresolvedParam` untested*: kept as recorded above; no project can reach it.
- *§1.1 row for `H0 ~ H1_0` is wrong*: confirmed, see above.
- *Scope creep* (overview note, compile test, `ParamsWidths`): kept. The reviewer judged all three
  justified or harmless.
- *The completeness test reuses `param_assignment`/`resolve_expr_value`*: kept. Those helpers
  predate the story and are shared with module generation; the expectation still comes from the
  game instances, not `params_inv`'s output, as §4.2 asks.
- *Two captured goal fixtures still show flat names*: recorded under follow-up.

After the fixes, `cargo test --lib writers::easycrypt` passed 275 and the full suites were rerun
(see Verification).

## State handed to the next story

- **Package-state type**: `<Pkg>_pkgstate`, fields `<Pkg>_<Names-mangled state field>`, declared
  only in `Eq_*_Invariants.ec`, one per package with state used in the equivalence, shared by both
  sides. Built by `register_pkg_state_type`.
- **Game record** `<Game>_state`:
  `{l_|r_}pkg_<Inst> : <Pkg>_pkgstate` (instances with state, `ordered_pkgs_idx()` order), then
  `{l_|r_}pkg_<Inst>_<mangled param>` (`param_needs_var` parameters, same order), then
  `{l_|r_}abort_flag`. Naming helpers: `invariant::{pkg_state_type_name, pkg_state_field_name,
  instance_field_name, param_field_name}`. `proof.rs::build_side_record_lit` uses them.
- **`.smt2` atoms**:
  - `left.KX.State` → ``l.`l_pkg_KX.`KX_d_State``
  - `left.KX.b` → ``l.`l_pkg_KX_b``
  - `(= left.KX right.KX)` → ``l.`l_pkg_KX = r.`r_pkg_KX``, or `true` (no state), or
    `PackageMismatch` (different packages).
- **`params_inv` rule** as in §3.4. On the synthetic project it gives exactly:

  ```
  op params_inv (l : L_state) (r : R_state) : bool =
       l.`l_pkg_OnlyL_b = true
    /\ l.`l_pkg_T_b1 = l.`l_pkg_T_b2
    /\ l.`l_pkg_Store_b = r.`r_pkg_Keep_flag
    /\ r.`r_pkg_OnlyR_flag = false
    /\ l.`l_pkg_Front_b = r.`r_pkg_Front_b
    /\ r.`r_pkg_T_b2 = true.
  ```

  The cases it covers: left-only literal (`OnlyL`), right-only literal (`OnlyR`), one constant
  under different instance and parameter names (`Store.b`/`Keep.flag`), the within-side chain
  (`T.b1`/`T.b2` on the left), and the only field bound to `w` (`r.T.b1`, absent).
- **New `InvariantError` variants**: `PackageStateMismatch { package }`,
  `PackageMismatch { file, left_instance, left_package, right_instance, right_package }`,
  `UnresolvedParam { game, instance, param }`, `FieldCollision { field }`.
- **Goldens**: `story42/4WHS/Eq_H1_1_H2_0_Invariants.ec` (new) and
  `story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` (regenerated). Nothing outside `Eq_*` changed in
  any export.
- **Exporting `testdata/easycrypt/story42/params` without `--theorem` fails by design**
  (`ParamsBad`, `ParamsWidths`, `ParamsClash`). Use `--theorem Params`.
- Two owner-run checks are left unchecked (see above).

## Notes for follow-up

- `src/writers/easycrypt/types.rs:101` **panics** (`bits-length identifier not resolved to a
  theorem const`) when a package instance binds a `Bits` width parameter to an integer *literal*
  in the composition (`instance K = Key { params { n: 256 } }`). I found this while building
  `ParamsWidths`, and that theorem binds the width through theorem constants instead. It should be
  a hard error with a span, or supported.
- Clippy warnings that predate this story are left alone: `src/debug/sweep.rs:199`, and the
  `tempfile::TempDir::into_path` deprecations with `cvc5-lib`.
- `build_side_record` (`invariant.rs`) and `build_side_record_lit` (`proof.rs`) walk the same
  instances, mangle the same names and order the same fields; only the naming helpers are
  shared. A small state-record layout module both use would remove the duplication and the
  `(binder, op_param, field_ns_prefix)` parameter triple (review finding, not done here).
- `testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json` and
  `testdata/easycrypt/story27/kem_dem_tactics_report.txt` are captured EasyCrypt goals that still
  show the old flat field names (`l_pkg_rand_ctr`). No test compares exports against them, so they
  are stale but harmless; recapture them if they are used again.
- `example-projects/*/_build/` is still not git-ignored. All exports for this story were written
  under `/tmp`.
