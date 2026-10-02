# Story 42 — `params_inv` states every package parameter, and package state excludes parameters

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 06, 07, **43** (do 43 first; this story's golden file is written in 43's layout).
**Blocks:** nothing.
**Records:** `docs/adr/0007-invariant-game-state-nests-package-state-records.md`.

---

## 1. Why this story exists

`domino easycrypt prove` on 4WHS `Full4WHS`, proofstep `H1_1 ~ H2_0`, leaves **10 admits**, all
`J1 side-goal [domino-verified-ec-failed] Domino: verified`
(`example-projects/4WHS/_build/easycrypt/Full4WHS/Eq_H1_1_H2_0.report.txt`). Every one of them is
the side goal of an `rcondf{2} ^if`, and every one has the same conclusion:

```
… => !Comp_H2.Cloned_Pkg_CR.CR.b{hr}
```

That is, the `if (b)` branch of package `CR` (`Pkg_CR.ec`) is not taken on the right. It holds:
the theorem instance `H2_0` binds `bcr: false`, and game `H2` passes it as `CR { b: bcr }`. In
EasyCrypt, `bcr` is an argument of `Exp_H2(A).run(b, false)`, which `Game_H2.init` stores in the
mutable global `Pkg_Inst_CR.b`. After `call (: inv …)` the oracle goals know only `inv`, and
`inv` does not say `CR.b = false`:

```
op params_inv l r = l.`l_pkg_Nonces_b = true /\ r.`r_pkg_Nonces_b = true /\ l.`l_pkg_KX_b = r.`r_pkg_KX_b.
```

### 1.1 The cause

`build_params_inv` (`src/writers/easycrypt/invariant.rs`) iterates over the left game's package
instances and pairs each one with the right instance **of the same name**. An instance with no
partner is skipped (`let Some(right_inst) = … else { continue; }`), and so are its literal pins,
which are emitted only inside a matched pair. `CR` exists only in `H2`, so nothing about it is
said. It then pairs parameters **by parameter name** within the matched instances, so a theorem
constant bound to differently-named parameters is never related either.

All the parameter fields that `params_inv` currently leaves unpinned in `Full4WHS` (from the
translated files on 2026-09-30):

| Hop | Missing | Shape |
|---|---|---|
| `H0 ~ H1_0` | `r.Nonces.b = true` | instance only on the right |
| `H1_1 ~ H2_0` | `r.CR.b = false` | instance only on the right (the 10 admits) |
| `H3_1 ~ H4` | `l.CR.b` | instance only on the left |
| `H5 ~ H6_0` | `r.PRF.b = false`; `l.KX.b = r.KX.btest = r.KX.bleast` | instance only on the right; same instance name `KX`, but packages `KX_nokey`/`KX_noprfkey` name the parameter differently, and all three are bound to theorem `b` |
| `H6_1_1 ~ H7_0` | `r.MAC.b` | instance only on the right |

### 1.2 A second defect: package equality compares parameters

`(= state-left.KX state-right.KX)` in a `.smt2` is expanded by `translate_instance_equality` into
an equality on **every** lookup key both instances share. Today the lookup holds parameters next
to state fields (`build_side_record` puts both into one flat record), so the expansion also
equates parameters. That is why `Domino_invariant` of `H1_1 ~ H2_0` contains
`l_pkg_KX_b = r_pkg_KX_b`. This is wrong in principle. In Domino, a package's state is its state
fields only (`CONTEXT.md`, *Package state*). `src/writers/smt/patterns/datastructures/pkg_state.rs`
gives the package-state sort one selector per `pkg.state` entry and none for parameters. A hop
whose two sides bind an idealization bit to different literals would get a translated invariant
containing `false = true`, which could never be proved even though Domino proves the hop.

### 1.3 Why it was missed

1. **The spec only covered instances that exist on both sides.** Story 06 §3.3: *"for each such
   package parameter **on both sides**, if both instances bind it to the same theorem constant,
   emit `l = r`; if an instance binds a literal, state it directly."* It never said what happens to
   an instance on one side only.
2. **The implementation paired by name and gave a reason that was only partly true.** Story 06's
   report §7: *"an equivalence's two sides always reuse the same instance names"*. That is true of
   the names that occur on both sides, not of the set of instances.
3. **The one known gap was the wrong one.** Report §11 recorded a single limitation: an instance
   *renamed* between the sides. It did not consider instances on one side only, or the same
   constant under different parameter names.
4. **Tests and goldens only used Simple4WHS.** The acceptance criteria, the only `params_inv` test
   (`real_hybrid3_ideal_hybrid3_params_inv_states_literals_directly`) and the only golden
   (`testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec`) all use Simple4WHS hops,
   whose two sides have identical instance sets and parameter names. Full4WHS, whose hops add and
   remove packages, was never checked. The whole-package expansion of §1.2 was tested
   (`whole_package_state_equality_expands_to_a_field_by_field_conjunction`), but only for packages
   whose parameters were equal on both sides, so the extra conjunct was invisible.

## 2. Inherited from earlier stories

- **Story 06** (`invariant.rs`):
  - `build_side_record` produces one flat `EcItem::Record` per side, with a field
    `{l_|r_}pkg_<Inst>_<field>` for each state field and for each parameter passing
    `package::param_needs_var`, then `{l_|r_}abort_flag`.
  - `add_side_field` indexes each field into the lookup as `"{left|right}.<Inst>.<raw name>"`.
  - `translate_atom` resolves dotted atoms (`left.KX.State`, also when the source spells its
    binders `state-left`) through that lookup.
  - `resolve_instance_atom` and `translate_instance_equality` expand `(= <side>.<Inst> <side>.<Inst>)`.
  - `build_params_inv` and `resolve_expr_value` (which walks a binding to a `ParamValue::Literal` or
    `ParamValue::TheoremConst`) produce `params_inv`.
  - Records need `l_`/`r_` prefixes because EasyCrypt record fields are global projection operators
    (story 06 report §2).
- **`package::param_needs_var`** (`src/writers/easycrypt/package.rs`): booleans, and integers not
  used as a width. These are the parameters that become fields. Function parameters and width
  integers are substituted into the code and never become fields.
- **Story 07** (`src/writers/easycrypt/proof.rs`): `build_side_record_lit` builds the `call`'s
  record literal with the same field names, reading `Comp_<G>.Pkg_Inst_<Inst>.<field>{1|2}`.
- **The tactics driver** unfolds `inv`, `params_inv` and the `Domino_<rel>` operators by name
  (`src/easycrypt/tactics/driver.rs`, `unfold_ops`; `src/easycrypt/tactics/mod.rs`) and never
  names a record field.
- **Story 43:** the block renderer for `op` bodies and record literals. Use it for every new item.
  Its implementation report says how to render a record literal nested in a field.
  Concretely (from story 43's implementation):
  - `render.rs::render_expr_block(e: &EcExpr, col: usize) -> String`. `render_op_def` already sends
    **every** `EcItem::OpDef` body through it, so a new `op` needs no layout code at all.
  - The `call` is the structured `ProofLine::InvariantCall { inv }` (`ast.rs`), built in
    `proof.rs` as `EcExpr::App { head: "inv", args: [left_lit, right_lit] }`. It is laid out by
    `render.rs::render_invariant_call`, which renders each argument with
    `render_record_block(e, col)`. For §3.5, make an `EcExpr::RecordLit` the *value* of the
    `l_pkg_<Inst>` field. The renderer starts it right after `l_pkg_KX = ` and lines its fields up
    under its own first field. Nothing in `proof.rs` formats text. The unit test
    `a_record_literal_puts_one_field_per_line_and_a_nested_one_under_its_field`
    (`src/writers/easycrypt/tests.rs`) shows the exact layout. A record literal inside an `op` body
    stays on one line.
  - `/\` and `\/` are right-associative. Build every `/\`/`\/`/`=>` chain with
    `EcExpr::right_chain(op, operands)` (`ast.rs`). `fold_and` in `invariant.rs` already does.
    `right_chain` splices a nested `/\`/`\/` chain into its parent, so a whole-package equality
    among other conjuncts prints flat.
  - `testdata/easycrypt/story06/4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec` is in story 43's layout.
    No golden contains `call (: inv`; the call's layout is pinned by `proof.rs`'s test
    `the_invariant_call_puts_each_record_on_its_own_line_and_one_field_per_line` (hello-world).
- **ADR 0006:** translating with `--force` deletes every session record, so a proof job after
  re-translation never resumes against the old invariant.

## 3. Work to do

Decisions below are the owner's (design session of 2026-10-03). Do not reopen them.

### 3.1 One state record type per package (ADR 0007)

`Eq_<L>_<R>_Invariants.ec` gets one record type per **package** (template) that has state fields
and is used by an instance on either side. It comes before the two game-state types:

```
type KX_pkgstate = {
  KX_d_LTK   : (int, bits_n) fmap;
  …
  KX_d_State : (int, (…)) fmap
}.
```

- Fields are the package's **state fields only**, prefixed with the package name (field names are
  global in EasyCrypt; two packages may both have a `State`). Mangle through `Names` as today, so a
  collision is a hard error, not a silent merge.
- Both sides share the type when they use the same package, including when both sides use the same
  composition.
- If two instances of the same package have **different field types** (different widths), that is a
  hard `InvariantError` naming the package. Nothing does this today.
- These types exist **only in the invariant file**. Package translation (`Pkg_*.ec`) is unchanged.

### 3.2 The game-state record

Each side's record (`<Game>_state`) becomes:

- one field `{l_|r_}pkg_<Inst> : <Pkg>_pkgstate` per instance **that has state fields**;
- one field `{l_|r_}pkg_<Inst>_<param>` per parameter passing `param_needs_var`, as today;
- `{l_|r_}abort_flag`.

A stateless instance contributes only its parameter fields.

### 3.3 Translating the `.smt2`

- **Dotted state field** `left.KX.State` → ``l.`l_pkg_KX.`KX_d_State``.
- **Dotted parameter** `left.KX.b` → ``l.`l_pkg_KX_b`` (the game record's parameter field). Domino's
  smtrewrite does not bind it today, so Domino rejects such a file before export runs. The
  translation exists so that it is correct if Domino starts binding it.
- **Whole-package equality** `(= state-left.KX state-right.KX)`:
  - both instances of the **same package**, both with state → ``l.`l_pkg_KX = r.`r_pkg_KX`` (one
    record equality, since they share the type);
  - both of the same package, **stateless** → `true`;
  - instances of **different packages** (e.g. `H5 ~ H6_0`'s `KX`, which is `KX_nokey` on the left
    and `KX_noprfkey` on the right) → hard `InvariantError` naming both packages. In Domino the
    `=` would be ill-sorted.
  
  Parameters are never part of this equality.
- Update `translate_instance_equality`'s doc comment, which today says it mirrors
  `build_params_inv`'s tolerance for asymmetric fields.

### 3.4 `params_inv`

Replace the name pairing in `build_params_inv` with a rule keyed by **what each field is bound to**:

1. Collect every parameter field of both sides: the left record's parameter fields in record order,
   then the right's. Resolve each binding with `resolve_expr_value`.
2. A field bound to a **literal** contributes `field = <literal>`.
3. Fields bound to the **same theorem constant** are chained: each field after the first one bound
   to that constant contributes `<previous field bound to it> = field`. This holds across sides
   and within one side, whatever the instance and parameter names (`H5 ~ H6_0`:
   ``l.`l_pkg_KX_b = r.`r_pkg_KX_btest /\ r.`r_pkg_KX_btest = r.`r_pkg_KX_bleast``).
4. A field that is the **only** one bound to its theorem constant contributes nothing. It holds for
   every value of the constant.
5. A binding that `resolve_expr_value` cannot resolve is a hard `InvariantError` naming the
   instance and parameter. It used to be skipped silently, which is how a gap like this one stays
   hidden. Story 06's comments say every binding is a literal or a bare constant; if a real
   project trips this, stop and report it.

Conjuncts appear in field-collection order. `op params_inv (l : <Left>_state) (r : <Right>_state) :
bool` keeps its signature, and `inv` is unchanged.

### 3.5 The `call`

`build_side_record_lit` (`proof.rs`) builds the nested literal to match §3.2:
`l_pkg_KX = {| KX_d_LTK = Comp_H1.Pkg_Inst_KX.d_LTK{1}; … |}`, parameter fields as today, then
`l_abort_flag`. Render it with story 43's record renderer.

### 3.6 Story 06's report

Append to `06-invariant-translation-IMPLEMENTATION-REPORT.md` §7 and §11 a dated note:
"Superseded by story 42: instances are no longer paired by name; see 42 §1.3." Do not rewrite
the original text.

## 4. Tests

### 4.1 Unit tests on a synthetic project

Add a small project under `testdata/easycrypt/story42/params/` (its own `ssp.toml`, packages,
games and a theorem), loaded the way `load_hybrid0_hybrid1` loads 4WHS. Its equivalences must cover,
each in its own test, with the expected EasyCrypt text asserted:

- a literal-bound parameter of an instance that exists **only on the left**, and one **only on the right**;
- one theorem constant bound to parameters with **different instance and parameter names** on the two sides;
- one theorem constant bound to **two parameters on the same side** (the within-side chain);
- a parameter that is the **only** one bound to its constant (no conjunct);
- a whole-package equality between instances of the same package that have state, giving one record
  equality with **no parameter conjunct**;
- the same between **stateless** instances, giving `true`;
- the same between **different packages**, giving a hard error;
- a dotted parameter atom `left.P.b`, giving the parameter field;
- a dotted state atom, giving the nested projection.

### 4.2 Completeness test over the real projects

One test that translates **every equivalence** of 4WHS `Simple4WHS` and `Full4WHS`. For each
parameter field of either game record it checks that the field is pinned to a literal in
`params_inv`, or equated in it to another field bound to the same theorem constant, or is the
**only** field bound to its constant. Compute the expectation from the game instances (instances,
`param_needs_var`, bindings), not from `params_inv`'s own output. This is the test that would have
caught §1.1.

### 4.3 Golden

`testdata/easycrypt/story42/4WHS/Eq_H1_1_H2_0_Invariants.ec`, generated from `Full4WHS`. Regenerate
the story 06 golden (its record shape changes) and every golden containing `call (: inv`.

## 5. Acceptance criteria

- [ ] §4's tests pass. The old `params_inv` and whole-package tests are updated or replaced, not
      deleted without replacement.
- [ ] `Full4WHS`'s regenerated `params_inv` operators contain every row of §1.1's table.
- [ ] No `Domino_<rel>` operator equates a parameter field, unless the `.smt2` names one with a
      dotted atom.
- [ ] Every `Eq_*_Invariants.ec` and every `Eq_*.ec` skeleton of `Simple4WHS` and `Full4WHS`
      compiles with `easycrypt compile`.
- [ ] `domino easycrypt --check-alignment` on `Simple4WHS` passes.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
- [ ] **Owner-run, not by the implementing session** (overview §7 forbids running `prove` on 4WHS):
      `Simple4WHS` `prove -f` has no more admits than before, and `Full4WHS` `H1_1 ~ H2_0` has 0
      `J1 side-goal` admits. Leave both unchecked in the report for the owner.

## 6. How to verify

```bash
cargo test --workspace easycrypt
cd example-projects/4WHS
$D easycrypt --theorem Full4WHS --force          # also deletes stale session records (ADR 0006)
grep -A12 'op params_inv' _build/easycrypt/Full4WHS/Eq_*_Invariants.ec
for f in _build/easycrypt/Full4WHS/Eq_*.ec; do easycrypt compile -I _build/easycrypt/Full4WHS "$f"; done
$D easycrypt --theorem Simple4WHS --check-alignment

# owner only:
$D easycrypt prove --theorem Full4WHS --proofstep <H1_1~H2_0> -f
grep -c 'J1 side-goal' _build/easycrypt/Full4WHS/Eq_H1_1_H2_0.report.txt     # expect 0
# owner, before merging to main: a full Full4WHS prove -f, no hop with more admits than before
```

## 7. Notes / risks

- **smt and nested records.** After `rewrite /inv`, smt sees through two levels of record literal
  (``{| l_pkg_KX = {| KX_d_LTK = …; … |}; … |}.`l_pkg_KX.`KX_d_LTK``). Simplification already
  reduces one level today, but the owner-run check in §5 is what shows whether the tactics driver's
  `auto => /#` ladder still closes the same goals. If it does not, record which goals and stop; do
  not add per-field unfolding lemmas without the owner.
- **Integer parameters and Domino's sorts.** Domino's package-state sort name encodes the instance's
  integer parameters (`only_ints` in `pkg_state.rs`), so in Domino two instances of one package with
  different integer parameters have different sorts. In EasyCrypt they share `<Pkg>_pkgstate`, so
  §3.3 accepts an equality Domino would reject. That is harmless, because Domino rejects the file
  first. Do not try to mirror it.
- **Package and game invariants** (`define-package-invariant`, `define-game-invariant`) are still
  skipped by translation (story 06 §3.2). §3.1's types are what a later story would use to translate them.

## 8. State handed to the next story

Record in `42-…-IMPLEMENTATION-REPORT.md`: the package-state type and field naming, the new
game-record shape, the `params_inv` rule as implemented (with the synthetic project's cases), the new
`InvariantError` variants, the goldens regenerated, and the two owner-run checks left unchecked.
