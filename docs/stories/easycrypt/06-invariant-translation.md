# Story 06 — Invariant translation (`Eq_*_Invariants.ec`)

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 02 (types/expressions), story 04 (game modules, state variable names).
**Blocks:** 07.

---

## 1. Why this story exists

An equivalence's invariant is hand-written SMT-LIB. EasyCrypt's `call` tactic needs the same
predicate as an EasyCrypt formula over both memories. The constructs used are a small, closed set,
and the owner confirmed the mapping: `forall` is `forall`, state accessors come from the
game-state record passed to the operator, `select`/`store` are fmap notation, tuple accessors are
EasyCrypt tuple projections, `maybe-get` is `oget`, `None` exists, and the theorem's global
functions are the operators from `Types.ec`.

## 2. Inherited from earlier stories

- Story 02: type translation, expression AST, `EcExportError`, and `Types.ec`'s `func_<name>`
  operator names.
- Story 04: for each composition, the package instances and the **module variable names** its state
  fields map to (mangled). The game-state record fields are derived from those.

### 2.1 Where invariants come from

On this branch an equivalence has exactly **one** invariant spec
(`src/parser/ssp.pest:295`: `equivalence = { kw_equivalence ~ identifier ~ identifier ~ "{" ~
invariant_spec ~ equivalence_oracle+ ~ "}" }`), so `Equivalence::invariants() -> &[String]` is one
list of file paths for the whole hop — not per oracle. Example:
`example-projects/4WHS/theorem/Simple4WHS.ssp:107` →
`./theorem/simple/invariant-Hybrid0-Hybrid1.smt2`.

### 2.2 The SMT parser that already exists

`src/util/smtparser` (grammar `smt.pest`) parses these forms:

```
defun                  = ( define-fun <atom> <list> <ty> <sexp> )
define_state_relation  = ( define-state-relation <atom> <list> <sexp> )
define_lemma           = ( define-lemma <atom> <list> <sexp> )
define_game_invariant  = ( define-game-invariant <sexp> )
define_package_invariant = ( define-package-invariant <sexp> )
sampleid               = ( sample-id <string> <string> <string> )
```

Atoms may contain `- = < > $ ! + @ . *`, so `left.KX.State`, `el11-10`, `<<func-prf>>`,
`is-mk-none` and `mk-tuple10` all arrive as single atoms.

### 2.3 What the real files contain

From `example-projects/4WHS/theorem/simple/invariant-Hybrid0-Hybrid1.smt2`: `define-state-relation`
with `(left right)`, `forall`, `let`, `ite`, `and`/`or`/`not`/`=>`/`=`, `>`/`>=`, `select`,
`is-mk-none`, `maybe-get`, `mk-some`, `(as mk-none (Maybe Bits_n))`, `mk-tuple10`, `el11-4`,
`<<func-prf>>`, and dotted state accessors `left.KX.State`.

## 3. Work to do

New file `src/writers/easycrypt/invariant.rs`, producing
`Eq_<LeftInst>_<RightInst>_Invariants.ec`.

### 3.1 The game-state records

One flat record per **game instance** of the hop, in this file:

```
type Hybrid0_state = {
  pkg_KX_d_LTK   : (int, bits_n) fmap;
  …one field per (instance, state field) in ordered_pkgs_idx() order…
  abort_flag     : bool;
}.
```

Field name is `pkg_<mangled instance>_<mangled field>`; the last field is `abort_flag`. Left and
right records live in one file, so they must have different type names — use the **game instance**
names (`Real_Hybrid3_state`, `Ideal_Hybrid3_state`), which differ even when both sides share a
composition. Record field names are globally unique per namespace in EasyCrypt (overview §8.1), so
prefixing with the instance is what keeps left and right from colliding; when both sides share a
composition the prefixes are the same, so add an `l_`/`r_` prefix in that case and record the rule.

### 3.2 SMT → EasyCrypt

| SMT | EasyCrypt |
|---|---|
| `(forall ((x Int) …) body)` / `exists` | `forall (x : int) …, body` / `exists` |
| `(let ((x e)) body)` | `let x = e in body` |
| `(ite c a b)` | `if c then a else b` |
| `and` / `or` / `not` / `=>` | `/\` `\/` `!` `=>` (n-ary folded left) |
| `=` with 2 args / n args | `a = b` / adjacent-pair conjunction |
| `> >= < <= + - *` | same |
| `(select A k)` | `A.[k]` |
| `(store A k v)` | `A.[k <- v]` |
| `(is-mk-none e)` | `e = None` |
| `(maybe-get e)` | `oget e` |
| `(mk-some e)` | `Some e` |
| `(as mk-none (Maybe T))` | `None<:T>` |
| `(mk-tupleN e1 … eN)` | `(e1, …, eN)` |
| `(elN-i e)` | `` e.`i `` |
| `<<func-f>>` applied to args | `func_f a1 a2 …` (curried) |
| `left.<Inst>.<Field>` / `right.…` | `` l.`pkg_<Inst>_<Field> `` / `` r.`…` `` |
| sorts `Int` `Bool` `Bits_n` `(Maybe T)` `(Array K V)` `(TupleN …)` | `int` `bool` `bits_n` `T option` `(K, V) fmap` `(… * …)` |

Anything else — including `define-lemma`, `define-game-invariant`, `define-package-invariant`, and
`randomness-mapping-*` / `sample-id` definitions — is **not** translated. `define-lemma` and the
randomness forms are *skipped with a comment in the output and a line on stdout*; an unrecognised
s-expression inside a translated definition is a **hard error** naming the file and the
s-expression. Never emit `true` for something you could not translate.

### 3.3 The operators

- Each `define-fun` becomes `op Domino_<mangled name> (args) : <ty> = <body>.`
- Each `define-state-relation <name> (left right) <body>` becomes
  `op Domino_<mangled name> (l : <Left>_state) (r : <Right>_state) : bool = <body>.`
- `params_inv` relates the idealization bits and value-integer parameters: for each such package
  parameter on both sides, if both instances bind it to the *same* theorem constant, emit
  `` l.`pkg_X_b = r.`pkg_Y_b ``; if an instance binds a literal, state it directly
  (`` l.`pkg_PRF_b = true ``). Derive this from the game instances' `consts` and the package
  instances' `params` — the same data story 04 used to build `init` calls.
- The assembled invariant:

```
op inv (l : Hybrid0_state) (r : Hybrid1_state) : bool =
     params_inv l r
  /\ l.`abort_flag = r.`abort_flag
  /\ (!l.`abort_flag => Domino_state_eq l r /\ Domino_keys_computed_correctly l r /\ …).
```

State relations are conjoined in file order. `params_inv` and the abort-flag equality hold
unconditionally; every translated state relation sits under `!abort_flag`.

## 4. Acceptance criteria

- [ ] `Eq_Hybrid0_Hybrid1_Invariants.ec` for 4WHS `Simple4WHS` is generated and **compiles**
      (`easycrypt compile`), given story 02/04 output. Golden file under
      `testdata/easycrypt/story06/`.
- [ ] Unit tests cover every row of §3.2, each as a small s-expression → expected EasyCrypt string.
- [ ] `el11-4` → `` e.`4 ``, and `mk-tuple10` with ten arguments round-trips.
- [ ] A `define-lemma` in an invariant file is skipped with a comment, not translated, and reported
      on stdout; an unknown atom inside a `define-state-relation` is a hard error naming the file.
- [ ] `params_inv` for `Hybrid0`/`Hybrid1` relates `b` on both sides (both bind the theorem constant
      `b`), and for `Real_Hybrid3`/`Ideal_Hybrid3` states the literals `false`/`true` directly.
- [ ] Both sides sharing a composition (`Real_Hybrid3` vs `Ideal_Hybrid3`) produces two distinct
      record types with non-colliding field names.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo test --workspace easycrypt
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
easycrypt compile -I _build/easycrypt/Simple4WHS _build/easycrypt/Simple4WHS/Eq_Hybrid0_Hybrid1_Invariants.ec
# reference only, do not copy: ~/Research/ec4whs/simple/Eq_Real_Hybrid3_Ideal_Hybrid3_Domino_Invariants.ec
```

## 6. Notes / risks

- **`oget` is not `maybe-get`.** SMT's `maybe-get` on `None` is underspecified; EasyCrypt's `oget`
  on `None` is `witness`. Both are "some unspecified value", so the translation is faithful, but do
  not add axioms about `oget None`.
- **Do not reorder conjuncts.** Keeping file order makes a failed `smt` call in story 07 traceable
  back to a line in the `.smt2`.
- **The record is a helper.** Nothing outside the invariant operators may mention it (overview §3);
  story 07 builds it inline at the `call` site.
- **Watch mangling of SMT names**: `keys-computed-correctly` → `Domino_keys_computed_correctly`;
  two SMT names differing only in `-` vs `_` collide and must be a hard error, not a silent merge.

## 7. State handed to the next story

Record in `06-…-IMPLEMENTATION-REPORT.md`: the record type and field naming (including the
same-composition `l_`/`r_` rule), the `Domino_` operator naming, the `inv`/`params_inv` signatures
story 07 must call, the list of SMT forms translated vs skipped, and the golden-file paths.
