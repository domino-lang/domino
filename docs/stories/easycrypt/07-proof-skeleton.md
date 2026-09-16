# Story 07 — Equivalence proof skeleton (`Eq_*.ec`)

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 05 (command + layout), story 06 (invariants).
**Blocks:** nothing.

---

## 1. Why this story exists

This is the artifact the whole export exists for: a file per equivalence holding the lemma, the
adversary declaration, the invariant `call`, the induction start, and an `admit` per oracle. The
owner is explicit that deriving the per-oracle tactics is **not** in scope here:

> I am not expecting you to generate a full proof deterministically and automatically. … I want you
> to generate these branching code and then put admit in the interesting parts.

v1 stops at `admit`. Stories 08/09 give the human the path information to fill them in.

## 2. Inherited from earlier stories

- Story 04: `Game_<Comp>`, `Exp_<Comp>`, `Iface_<X>`, `Adv_<X>`, the `init` parameter order per
  composition, **the exact restriction strings** (`-<Game>.Pkg_<inst>.<Variant>`, `-<Game>.Game_<Comp>`)
  and the **export order** per game interface — the proof bullets follow that order.
- Story 06: `Eq_<L>_<R>_Invariants.ec` with `<L>_state`, `<R>_state`, `params_inv` and `inv`. Entry
  point: `invariant::build_invariant_file(theorem, equivalence, project) ->
  Result<InvariantFile, EcExportError>` (`src/writers/easycrypt/invariant.rs`); not wired into
  `export::export_theorem`/the CLI yet — this story's own job. **The field-naming rule in §3.1's
  worked example below (bare `pkg_KX_d_LTK`) is wrong — do not copy it.** Every field on the left
  record is `l_pkg_<instance>_<mangled field>` and every field on the right is
  `r_pkg_<instance>_<mangled field>` (and `l_abort_flag`/`r_abort_flag`), **unconditionally**, not
  only "when both sides share a composition": `abort_flag` alone collides between any two records in
  one file regardless (verified against real `easycrypt` — two record types can never share a field
  name, full stop), and `Hybrid0`/`Hybrid1` additionally collide on several real `KX`-instance state
  field names despite being different compositions. `<mangled field>` is
  `Names::mangle(NameKind::Var, raw_name)` — the same mangling `package.rs`'s own module-`var`
  rendering already gave that field/param, so this story's inline record literal
  (`{| l_pkg_KX_d_LTK = Hybrid0.Pkg_KX.KX.d_LTK{1}; …; l_abort_flag = Hybrid0.Game_Hybrid0.abort_flag{1} |}`)
  can re-derive each field's name by re-running the same mangling, without needing story 06's own
  internal lookup map. Record fields cover `Package::state` **and** every qualifying
  `Package::params` entry (`package::param_needs_var` — a package's own `Boolean`/non-width-`Integer`
  param, stored as a persistent module `var` by story 03), in that order, then `abort_flag` — not
  just `Package::state` alone. `params_inv`/`inv` are fixed, unmangled op names (`op params_inv (l :
  <L>_state) (r : <R>_state) : bool` / `op inv (l : <L>_state) (r : <R>_state) : bool`). Two
  shared-infrastructure facts this story discovered while getting its own output to compile, that
  apply here too: (1) `render.rs`'s `Eq`/`Ne` are non-associative in EasyCrypt's own grammar (`a = b
  = c` is a parse error) and `render.rs` now parenthesizes both sides of a nested `Eq`/`Ne` — already
  fixed in shared code, nothing to redo; (2) `EcBinop::Gt`/`Ge` are not usable for `int`/`Bits`
  comparisons (`>`/`>=` resolve only via `Real` in EasyCrypt's base theories) — if this story ever
  needs to render a numeric `>`/`>=` itself, flip it to `<`/`<=` with swapped operands, the same way
  `types.rs` and `invariant.rs` both already do.
- Story 05: `export_theorem` and where files land.
- Story 01 §3.1 permits this story to add `EcExpr::Pr { module, proc, args, memory, event }` to
  `ast.rs`; do that rather than emitting `Pr[…]` as raw text.

### 2.1 Where equivalences come from

`Theorem::game_hops`, filtered with `GameHop::as_equivalence()`. `Equivalence` gives
`left_name()`, `right_name()`, `invariants()` and `trees() -> &[(String, Vec<Claim>)]` — oracle
name → claims (`invariant`, `same-output`, `equal-aborts`, each with dependencies such as
`no-abort`). v1 does not translate claims individually; `trees()` is used only to know **which
oracles** the hop covers, and to warn if that set differs from the game interface's export list.

### 2.2 Verified proof syntax

This compiled in the design session against EasyCrypt r2026.06-12-g7e192dd:

```
section.
declare module A <: Adv { -GameH.G, -GameH.Pkg_KX.KX, -GameH.Pkg_Prot.Prot }.
lemma l &m b : Pr[Exp_H(A).run(b) @ &m : res] = Pr[Exp_H(A).run(b) @ &m : res].
proof.
byequiv => //. proc; inline.
call (: ={GameH.G.abort_flag, GameH.Pkg_KX.KX.t}).
proc; inline. admit.
auto.
qed.
end section.
```

## 3. Work to do

New file `src/writers/easycrypt/proof.rs`, producing `Eq_<LeftInst>_<RightInst>.ec` per
equivalence hop.

### 3.1 The file

```
require import AllCore Distr FMap Int IntDiv Types Interfaces.
require Hybrid0 Hybrid1.
require import Eq_Hybrid0_Hybrid1_Invariants.

section.

declare module A <: Interfaces.Adv_Hybrid0 { -Hybrid0.Game_Hybrid0, -Hybrid0.Pkg_KX.KX,
                                             -Hybrid0.Pkg_Prot.Prot, -Hybrid1.Game_Hybrid1,
                                             -Hybrid1.Pkg_KX.KX_NoKeys, -Hybrid1.Pkg_Prot.Prot_NoKey }.

lemma Hybrid0_Hybrid1_equiv &m (b : bool) :
  Pr[Hybrid0.Exp_Hybrid0(A).run(b) @ &m : res] =
  Pr[Hybrid1.Exp_Hybrid1(A).run(b) @ &m : res].
proof.
byequiv => //.
proc; inline.
call (: inv {| pkg_KX_d_LTK = Hybrid0.Pkg_KX.KX.d_LTK{1}; …; abort_flag = Hybrid0.Game_Hybrid0.abort_flag{1} |}
           {| … {2} … |}); last first.

auto => />.
smt(emptyE map_empty).

(* d_NewKey *)
+ proc; inline. admit.

(* d_NewSession *)
+ proc; inline. admit.
…
qed.

end section.
```

Rules:

- **Lemma name**: `<LeftInst>_<RightInst>_equiv`, mangled.
- **Binders**: `&m`, then one typed binder per theorem constant of boolean / value-integer type that
  either side's game instance binds to a *constant* rather than a literal, in theorem declaration
  order. Width integers and `fn` constants never appear (they are types and global operators).
- **`Pr` arguments**: each side's `Exp_<Comp>.run` arguments come from that **game instance's**
  `consts` — a literal binding renders as the literal (`false`), a theorem-constant binding renders
  as the matching lemma binder. This is what makes `Real_Hybrid3` vs `Ideal_Hybrid3` come out as
  `run(false, true)` vs `run(true, true)` over the *same* composition.
- **Restrictions**: every router and every instance clone of **both** sides, in the strings story 04
  recorded. When both sides share a composition, list it once.
- **The `call` invariant** builds both game-state records inline from module variables, tagged
  `{1}` / `{2}`, in the record's field order.
- **Induction start**: `last first.` then `auto => />.` then `smt(emptyE map_empty).` — a real
  `smt` call, not `admit`, so a broken base case is visible immediately (overview §3).
- **One bullet per exported oracle**, in the game interface's export order, each preceded by a
  comment naming the oracle and containing exactly `proc; inline. admit.`
- If `trees()` covers a different oracle set than the interface exports, emit a comment and a
  stdout warning naming the difference; do not silently drop an oracle.

### 3.2 Reporting

Extend story 05's stdout block with one line per equivalence: the file written, the oracle count,
and the admit count (= oracle count in v1).

## 4. Acceptance criteria

- [ ] For 4WHS `Simple4WHS`, `Eq_Hybrid0_Hybrid1.ec`, `Eq_Hybrid1_Hybrid2.ec` and
      `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` are generated; the reduction hop `Hybrid2 ~ Hybrid3` is
      skipped with a note.
- [ ] **The whole exported theorem compiles**: every file, in dependency order, with
      `easycrypt compile`, with `admit`s and no errors. This is the epic's acceptance criterion.
      The test skips when `easycrypt` is absent.
- [ ] `Eq_Real_Hybrid3_Ideal_Hybrid3.ec` shows both sides over one composition with different
      literal `run` arguments, and lists the shared composition's modules once in the restriction.
- [ ] The base case is a real `smt(…)` call; if it fails for 4WHS, record that in the
      implementation report with the goal — do **not** paper over it with `admit`.
- [ ] Bullet order matches the game interface export order exactly.
- [ ] `kem-dem` and `hello-world` also produce compiling `Eq_*.ec` files.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
cd _build/easycrypt/Simple4WHS
for f in Types.ec Interfaces.ec packages/*.ec games/*.ec Eq_*_Invariants.ec Eq_*.ec; do
  easycrypt compile -I . -I packages -I games $f || { echo "FAILED: $f"; break; }
done
```

> `domino easycrypt` on 4WHS is allowed; `domino prove`/`debug` on 4WHS is not.

## 6. Notes / risks

- **`last first` ordering.** `call (: inv …); last first.` puts the induction start first and the
  per-oracle goals after, in interface order. If EasyCrypt presents them in a different order than
  expected, fix the bullet order to match reality and record it — do not guess.
- **The base case may genuinely fail.** `smt(emptyE map_empty)` is what the manual translation uses;
  if a 4WHS state relation needs more lemmas, report the goal rather than widening the `smt` call
  blindly.
- **Do not attempt tactics per oracle.** No `sp`, no `rcondt`, no `match` — that is deliberately
  left to the human, informed by stories 08/09.
- **Restriction completeness**: a missing module in `{ -… }` fails late and confusingly. Generate
  the list from story 04's recorded strings, not by re-deriving it here.

## 7. State handed to the next story

Record in `07-…-IMPLEMENTATION-REPORT.md`: the emitted file shape, the binder/`Pr`-argument rule,
the bullet order actually accepted by EasyCrypt, whether the 4WHS base case discharged (with the
goal if not), and the full list of exported files that compile today.
