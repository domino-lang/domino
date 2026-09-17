# Story 15 — `byequiv` precondition via `arg`, not per-parameter conjuncts

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 13 (the precondition), story 14 (current module naming).
**Blocks:** nothing.

---

## 1. Why this story exists

Story 13 emits one conjunct per `run` parameter, naming the parameter directly:

```
byequiv
  (: ={glob A}
     /\ b{1} = b
     /\ b{2} = b
     ==> _) => //.
```

**When a lemma binder has the same name as a `run` parameter, the conjunct silently becomes
vacuous.** `b` is both the experiment's first parameter *and* the lemma binder derived from the
theorem constant `b`. EasyCrypt resolves the untagged name first: `b{1}` is typed as the *logical*
binder, the `{1}` memory tag is discarded, and the conjunct degenerates from "side 1's argument is
`b`" to `b = b` — true for any argument. The precondition ends up being just `={glob A}`.

EasyCrypt does not reject this. It emits a warning and carries on:

```
[warning] [Eq_H4_H5.ec:18] unused memory `&1', while typing b
[warning] [Eq_H4_H5.ec:18] unused memory `&2', while typing b
```

### 1.1 It bites for real, on real hops

Compiled against `r2026.06-12-g7e192dd`, on the actual output of
`domino easycrypt --theorem Full4WHS`:

| File | Binder / params | Warning? | Base case |
|---|---|---|---|
| `Eq_H4_H5.ec` | binder `b`, params `b` | **yes, both sides** | fails |
| `Eq_H0_H1_0.ec` | binder `b`, params `b` / `b, bnonce` | **yes, both sides** | fails |
| `Eq_H6_1_0_H6_1_1.ec` | binder `b`, params `bleast, bprf, btest` | no | compiles clean |

The one hop with no name overlap is the one with no warning — and the only one of the three whose
base case discharges.

### 1.2 The fix turns a failing hop into a passing one

`arg` is EasyCrypt's name for the tuple of a procedure's arguments. It is a *program* identifier,
so a logical binder cannot shadow it. Rewriting `Eq_H4_H5.ec`'s precondition — **changing nothing
else, not even the binder's name** — makes the whole file compile clean, base case included:

```
lemma H4_H5_equiv &m (b : bool) :
  Pr[Comp_H4.Exp_H4(A).run(b) @ &m : res] = Pr[Comp_H5.Exp_H5(A).run(b) @ &m : res].
proof.
byequiv
  (: ={glob A}
     /\ arg{1} = b
     /\ arg{2} = b
     ==> _) => //.
```

Verified: no warning, no `cannot prove goal (strict)`.

`Eq_H0_H1_0.ec` with `arg{1} = b /\ arg{2} = (b, false)` also loses the warning, but its base case
still fails — that is story 13 §1.1's *separate*, already-recorded cross-composition gap (H0 and H1
have structurally different game-state records) and is **not** this story's problem. Do not chase it.

## 2. Inherited from earlier stories

- `proof.rs:339` `side_precondition_conjuncts(comp, args, side, binder_mangled)` — builds today's
  per-parameter conjuncts.
- `proof.rs:321` `run_param_names(comp)` — re-derives `Exp_<Comp>.run`'s parameter spelling by
  mangling `comp.consts` through the same `composition_const_needs_arg` filter `game.rs` uses. After
  this story it has **no callers left**; delete it (and the `debug_assert_eq!` at `:346` that pairs
  it against `side_run_args`).
- `proof.rs:375` `build_byequiv_precondition(...)` — assembles `[GlobEq("A")] ++ side1 ++ side2`.
- `proof.rs:259` `side_run_args(comp, game_inst) -> Vec<RunArgValue>` — the resolved argument values,
  in `run` order. **This stays**; it is the only input the new form needs.
- `ast.rs:322` `ProofLine::ByequivPrecondition { conjuncts: Vec<EcExpr> }` and `ast.rs:221`
  `EcExpr::GlobEq(String)`; `render.rs:403` renders one conjunct per line. All unchanged.
- `EcExpr::Qualified { path, mem }` renders `<path>{mem}`; `EcExpr::Tuple` already exists. Between
  them the new conjunct needs no new AST node.

## 3. Work to do

### 3.1 One conjunct per side

Replace `side_precondition_conjuncts` with a function that emits **at most one** conjunct per side:

| side's `run` arity | conjunct |
|---|---|
| 0 | *(none — omit the side entirely)* |
| 1 | `arg{side} = <value>` |
| n > 1 | `arg{side} = (<v1>, <v2>, …, <vn>)` |

**A single argument is not a one-tuple.** `arg{1} = b` is right; `arg{1} = (b)` is the same thing
only because EasyCrypt's parentheses are grouping, so emit the bare value and don't rely on it.

Values come from `side_run_args` exactly as they do today: `RunArgValue::Literal(text)` through
`literal_text_to_expr`, `RunArgValue::TheoremConst(name)` through `binder_mangled[name]`. That is
the same `args_to_exprs` mapping (`proof.rs:282`) the `Pr[…]` arguments already use — reuse it
rather than writing the match a third time.

A composition with no `run` arguments contributes nothing, so a hop where both sides take none emits
`(: ={glob A} ==> _)`. Verified to compile.

### 3.2 Protect the name `arg`

`arg` is not in `names.rs`'s `KEYWORDS` list, so a Domino theorem constant spelled `arg` would
mangle to `arg` and reintroduce exactly the shadowing this story removes — `arg{1} = arg`. Add
`arg` to the set of names that get the `d_` prefix (alongside the keyword list and `ec_`), and a
mangling unit test for it. Keep the list sorted; `names.rs`'s own `keywords_are_sorted` test checks
that.

### 3.3 Leave the lemma binders alone

The `arg` form fixes the shadowing on its own — verified above with the binder still spelled `b`.
**Do not rename binders to `bit1`/`bit2`.** Keeping them spelled after the Domino theorem constant
is what lets a human line the EasyCrypt lemma up against the `.ssp` theorem, which is the whole
point of the export. Renaming is now *safe*, but it is not needed, and it costs traceability.

(If the owner later wants generic binder names, that is a one-line change in the
`binder_names.mangle(NameKind::Var, name)` call at `proof.rs:443` — a separate decision, not this
story.)

### 3.4 Retire the base-case tolerance where it is no longer needed

`Eq_H4_H5.ec` now compiles clean. Check every `Eq_*.ec` across `Simple4WHS`, `Full4WHS` and
`kem-dem-cca-ssp` and move each newly-clean file off
`test_support::assert_compiles_or_known_base_case_gap` onto plain `assert_compiles`, the way story
13 already did for `Eq_Real_Hybrid3_Ideal_Hybrid3.ec`. Update that helper's doc comment with the
list that genuinely still needs it.

## 4. Acceptance criteria

- [ ] No generated `Eq_*.ec` compiles with an `unused memory` warning. Assert it: the compile
      helper should fail on `unused memory` in `easycrypt`'s output, not just on a non-zero exit.
- [ ] `Eq_H4_H5.ec` compiles with plain `assert_compiles` — no tolerance, base case discharged.
- [ ] `Eq_H0_H1_0.ec` renders `arg{1} = b` and `arg{2} = (b, false)`; its remaining failure is the
      base case only, and the implementation report says so.
- [ ] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` still compiles clean, now as
      `arg{1} = (false, true)` / `arg{2} = (true, true)`.
- [ ] A one-argument side renders `arg{n} = <value>`, not `arg{n} = (<value>)`.
- [ ] A theorem constant named `arg` mangles to `d_arg`, with a unit test.
- [ ] `run_param_names` is deleted and nothing references it.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Full4WHS
cd _build/easycrypt/Full4WHS
for f in Eq_*.ec; do
  echo "== $f"
  easycrypt compile -I . "$f" 2>&1 | tr '\r' '\n' | grep -v '^\[.\] \[' \
    | grep -E "unused memory|critical"
done
```

Expect: **no `unused memory` lines at all**, and `critical … cannot prove goal (strict)` only on the
cross-composition hops story 13 §1.1 already lists.

> `domino easycrypt` on 4WHS is allowed; `domino prove`/`debug` on 4WHS is not.

## 6. Notes / risks

- **The warning is the only signal.** EasyCrypt accepts the broken form silently apart from
  `unused memory`. That is why acceptance criterion 1 asks the test helper to treat that warning as
  a failure — without it, this class of bug comes back invisibly.
- **`arg` refers to the procedure being reasoned about**, which after `byequiv` is
  `Exp_<Comp>.run` on each side. It is not affected by `proc; inline.` later in the proof, because
  the precondition is fixed at the `byequiv` line.
- **Argument order is the composition's.** `side_run_args` iterates `comp.consts` filtered by
  `composition_const_needs_arg`; the tuple must be built in exactly that order so it lines up with
  the `run(…)` arguments in the `Pr[…]` terms.
- **Do not collapse the two sides.** `arg{1} = arg{2}` is tempting when both sides take the same
  values, but the two sides can have different arities (H0 takes one argument, H1 takes two), and
  the explicit form is what the per-oracle goals need.
- **Out of scope, but noticed:** `domino easycrypt` on `example-projects/hello-world` currently
  fails with `unsupported SMT sort <GameState_MediumComposition_<$<!n!>$>>` from
  `theorem/invariant.smt2`. That is an invariant-translation problem, unrelated to this story —
  record it under "Notes for follow-up", do not fix it here.

## 7. State handed to the next story

Record in `15-…-IMPLEMENTATION-REPORT.md`: the rendered precondition for every hop of `Simple4WHS`
and `Full4WHS`, which files moved off the tolerance helper, and confirmation that no generated proof
produces an `unused memory` warning.
