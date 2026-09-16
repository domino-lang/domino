# Story 13 — `byequiv` relational precondition (and the duplicate `qed.`)

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 07 (`Eq_*.ec`). Do **after** story 10, which moves the goldens.
**Blocks:** nothing.

---

## 1. Why this story exists

Story 07 emits a bare `byequiv => //.` (`src/writers/easycrypt/proof.rs:443`). That leaves the
relational precondition entirely to EasyCrypt's default, which does **not** relate the two
adversaries' state, and does **not** bind either side's `run` arguments. Both are needed: the
induction start has to know the two games were initialised with the specific constants the lemma's
`Pr[…]` terms passed, and every per-oracle goal has to know the adversary is the same on both sides.

The shape the owner wants:

```
lemma Real_Hybrid3_Ideal_Hybrid3_equiv &m :
  Pr[Comp_Hybrid2.Exp_Hybrid2(A).run(false, true) @ &m : res] =
  Pr[Comp_Hybrid2.Exp_Hybrid2(A).run(true,  true) @ &m : res].
proof.
byequiv
  (: ={glob A}
     /\ b{1} = false
     /\ bprf{1} = true
     /\ b{2} = true
     /\ bprf{2} = true
     ==> _) => //.
```

### 1.1 This fixes a real, currently-failing goal

Verified against r2026.06-12-g7e192dd on the actual generated 4WHS output:

- **Before:** `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` fails with
  `[critical] cannot prove goal (strict)` at the `smt(emptyE map_empty).` base case.
- **After** adding exactly the precondition above (and nothing else): the file compiles clean. The
  base case discharges.

So `test_support::assert_compiles_or_known_base_case_gap` (`src/writers/easycrypt/mod.rs:85`) — the
helper story 07 added to tolerate `cannot prove goal (strict)` — is at least partly obsolete.

**It does not fix everything.** With the analogous precondition (`={glob A} /\ b{1} = b /\ b{2} = b`),
`Eq_Hybrid0_Hybrid1.ec` and `Eq_Hybrid1_Hybrid2.ec` still fail the base case. Those are
*cross-composition* hops where the two sides' package state differs structurally, and the residual
gap is in `params_inv` / the state relation, not in the precondition. **Do not widen the `smt` call
to chase them** — record the goal in the implementation report and leave the tolerance helper in
place for those two.

### 1.2 The duplicate `qed.`

Every generated `Eq_*.ec` ends with `qed.` twice:

```
+ proc; inline. admit.
qed.
qed.

end section.
```

`render_lemma` already appends `qed.` after the proof lines (`render.rs:355`), and `proof.rs:457`
pushes another one into the proof-line list. Delete the one in `proof.rs`. Folded into this story
because it touches the same function and the same goldens (owner's decision, Q7).

## 2. Inherited from earlier stories

- `side_run_args(comp, game_inst) -> Vec<RunArgValue>` (`proof.rs:278`) — iterates `comp.consts`,
  filtered by `composition_const_needs_arg`, and resolves each to `RunArgValue::Literal(text)` or
  `RunArgValue::TheoremConst(name)`. This is already the exact list, in the exact order, that
  `Exp_<Comp>.run` takes.
- `args_to_exprs(values, binder_mangled)` (`proof.rs:301`) turns those into the `Pr[…]` arguments;
  `binder_mangled` maps a theorem-constant name to its mangled lemma binder.
- Story 04 names each `run` parameter by mangling the composition-constant name with
  `Names::mangle(NameKind::Var, …)`. This story re-derives those names the same way, exactly as
  story 07 re-derives the game-state record field names rather than threading a lookup map through.
- `EcLemma.proof: Vec<ProofLine>`, rendered by `render_lemma` (`render.rs:338`), with
  `plain_line` / `bullet_line` / `blank_line` helpers in `proof.rs`.

## 3. Work to do

### 3.1 Build the precondition

For each side, zip the composition's `run` parameter names (mangled, in `side_run_args` order)
with that side's `RunArgValue`s, and emit one conjunct per parameter:

- `RunArgValue::Literal(text)` → `<param>{side} = <literal>`
- `RunArgValue::TheoremConst(name)` → `<param>{side} = <mangled lemma binder>`

Conjuncts in order: `={glob A}`, then **every** parameter of side 1, then every parameter of side 2.

**List every parameter of both sides, unconditionally** (owner's decision, Q6) — including the case
where both sides bind the same lemma binder, which renders as `b{1} = b /\ b{2} = b` rather than
`={b}`. Uniform, never under-specified, and it is what the per-oracle goals will need.

If a composition takes no `run` arguments, the precondition is just `(: ={glob A} ==> _)`.

### 3.2 Render it

```
byequiv
  (: ={glob A}
     /\ b{1} = false
     …
     ==> _) => //.
```

One conjunct per line, as above — a 4WHS composition can take several constants and a single line
gets long. The postcondition is the literal `_`.

This needs an AST node or a `ProofLine` variant that can carry a multi-line tactic; story 01 §3.1's
precedent (story 07 adding `EcExpr::Pr`) applies — add the node rather than emitting raw text with
embedded newlines, so story 08's lowering has something structured to read.

### 3.3 Remove the extra `qed.`

Delete `proof.rs:457`. `render_lemma` is the single owner of the closing `qed.`.

### 3.4 Revisit the base-case tolerance

`Eq_Real_Hybrid3_Ideal_Hybrid3.ec` must now compile with plain `assert_compiles`. Keep
`assert_compiles_or_known_base_case_gap` for the two cross-composition hops, and narrow its doc
comment (`mod.rs:73-84`) to say which hops still need it and why.

## 4. Acceptance criteria

- [ ] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` compiles with **`assert_compiles`**, no tolerance — the
      `smt(emptyE map_empty)` base case genuinely discharges.
- [ ] Its `byequiv` reads exactly the shape in §1, with `false`/`true` literals per side.
- [ ] `Eq_Hybrid0_Hybrid1.ec` renders `b{1} = b /\ b{2} = b` (same binder, both sides listed).
- [ ] Exactly one `qed.` per lemma in every generated `Eq_*.ec`.
- [ ] The two cross-composition hops still export and still fail only at the base case; the failing
      goal is recorded verbatim in the implementation report.
- [ ] `hello-world` and `kem-dem-cca-ssp` `Eq_*.ec` files still compile.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
cd _build/easycrypt/Simple4WHS
grep -c "^qed\.$" Eq_Real_Hybrid3_Ideal_Hybrid3.ec        # expect 1
easycrypt compile -I . Eq_Real_Hybrid3_Ideal_Hybrid3.ec   # expect clean
easycrypt compile -I . Eq_Hybrid0_Hybrid1.ec              # expect the base-case gap only
```

> `domino easycrypt` on 4WHS is allowed; `domino prove`/`debug` on 4WHS is not.

## 6. Notes / risks

- **Do not change the per-oracle bullets.** They stay `proc; inline. admit.` — deriving tactics is
  stories 08/09's job (overview §3).
- **Do not widen `smt(emptyE map_empty)`.** If a hop's base case still fails, that is information
  about the state relation, and silently adding lemmas to the `smt` call destroys it.
- **`=> //.` still belongs after the precondition.** It is what the owner's own snippet uses and it
  is what was verified to compile; do not replace it with `by` or drop it.
- **Parameter order is the composition's, not the game instance's.** `side_run_args` already
  iterates `comp.consts`; the precondition must use the same order so `<param>{n}` lines up with the
  `run(…)` argument at the same position.

## 7. State handed to the next story

Record in `13-…-IMPLEMENTATION-REPORT.md`: the rendered precondition for all three 4WHS hops, which
hops now compile cleanly, the exact residual goal for those that do not, and whether
`assert_compiles_or_known_base_case_gap` still has callers.
