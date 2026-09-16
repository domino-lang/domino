# Story 02 — Types, expressions and `Types.ec`

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 01 (`src/writers/easycrypt/{ast,render,names}.rs`).
**Blocks:** 03, 06.

---

## 1. Why this story exists

Everything downstream translates Domino types and expressions: package state and oracle bodies
(03), router signatures (04), invariants (06). This story writes that translation once, plus the
per-theorem `Types.ec` that declares the bits types, their constants and distributions, and the
theorem's function constants.

## 2. Inherited from earlier stories

### 2.1 From story 01

`EcType`, `EcExpr`, `EcItem`, `EcFile`, the renderer, and `Names::mangle`. Read its implementation
report first — if a variant you need is missing, add it to `ast.rs` and say so in your report.

### 2.2 Domino types (`src/types.rs:103`)

```rust
pub enum TypeKind {
    Unknown, Empty, Integer, String, Boolean,
    Bits(CountSpec), AddiGroupEl(String), MultGroupEl(String),
    List(Box<Type>), Set(Box<Type>), Tuple(Vec<Type>),
    Table(Box<Type>, Box<Type>), Maybe(Box<Type>),
    Fn(Vec<Type>, Box<Type>), UserDefined(String),
}
pub enum CountSpec { Identifier(Box<Identifier>), Literal(u64), Any }
```

### 2.3 Domino expressions (`src/expressions.rs:436`)

`Bot, Sample(Type), StringLiteral, IntegerLiteral, BooleanLiteral, BitsLiteral(String, Type),
Identifier, EmptyTable(Type), TableAccess(Identifier, Expression), Tuple, List, Set,
FnCall(Identifier, Vec<Expression>), None(Type), Some, Unwrap, Not, Neg, Inv, Add, Sub, Mul, Div,
Pow, Mod, LessThen, GreaterThen, LessThenEq, GreaterThenEq, Equals(Vec<Expression>), And(Vec),
Or(Vec), Xor(Vec), Sum, Prod, Any, All, Union, Cut, SetDiff, Concat`.

### 2.4 Where the bits types come from

`type_extract` (`src/transforms/type_extract.rs`) already collects every type a game instance
mentions into `GameInstAux.types: HashSet<Type>` (`src/transforms/theorem_transforms.rs:36`). The
export runs `EquivalenceTransform` (story 05 wires this up; for this story take the `Aux` as input)
and unions the sets over all of the theorem's game instances.

`example-projects/simple-KEM-example` is the only project using a **literal** width (`Bits(256)`);
everything else uses identifiers. `Bits(*)` (`CountSpec::Any`) appears in the type system and must
be handled.

## 3. Work to do

New file `src/writers/easycrypt/types.rs` (type + expression translation) and
`src/writers/easycrypt/typesfile.rs` (the `Types.ec` builder).

### 3.1 Type translation

| Domino | EasyCrypt |
|---|---|
| `Integer` | `int` |
| `Boolean` | `bool` |
| `Empty` | `unit` |
| `Bits(Identifier(n))` | `bits_<n>` |
| `Bits(Literal(256))` | `bits_256` |
| `Bits(Any)` | `bits` |
| `Maybe(T)` | `T option` |
| `Table(K, V)` | `(K, V) fmap` |
| `Tuple([a, b, …])` | `(a * b * …)` |
| `Fn(args, ret)` | curried `a -> b -> ret` |
| `String`, `List`, `Set`, `AddiGroupEl`, `MultGroupEl`, `UserDefined`, `Unknown` | **hard error** |

The bits type name is `bits_` followed by the width identifier with `-` → `_`; it always starts
lowercase, so it needs no further mangling. A `Tuple` of one element cannot occur (EasyCrypt has no
1-tuples); assert it and error if the parser ever produces one.

### 3.2 Expression translation

| Domino | EasyCrypt |
|---|---|
| `IntegerLiteral(n)` / `BooleanLiteral` | `n` / `true`\|`false` |
| `Bot` | `tt` |
| `BitsLiteral("0", Bits(n))` / `("1", …)` | `zero_n` / `one_n` |
| `BitsLiteral("empty", Bits(*))` | `zero` |
| `Identifier(id)` | mangled variable or module-qualified state name (caller supplies a resolver) |
| `None(T)` | `None<:T>` |
| `Some(e)` | `Some e` |
| `Unwrap(e)` | `oget e` |
| `EmptyTable(_)` | `empty` |
| `TableAccess(t, k)` | `t.[k]` — result type is already `V option`, matching Domino's `Maybe(V)` |
| `Tuple(es)` | `(e1, e2, …)` |
| `FnCall(f, args)` | curried application `f a1 a2 …` |
| `Not` / `Neg` | `!e` / `-e` |
| `Add/Sub/Mul` | `+ - *` |
| `Div` / `Mod` | `%/` / `%%` (`IntDiv`) |
| `LessThen`/`LessThenEq`/`GreaterThen`/`GreaterThenEq` | `<` `<=` `>` `>=` |
| `And(es)` / `Or(es)` / `Xor(es)` | left-folded `/\` `\/` `^^` |
| `Equals([a, b])` | `a = b` |
| `Equals([a, b, c, …])` | `a = b /\ b = c /\ …` (adjacent pairs) |
| `Inv`, `Pow`, `Sum`, `Prod`, `Any`, `All`, `Union`, `Cut`, `SetDiff`, `Concat`, `List`, `Set`, `StringLiteral` | **hard error** |
| `Sample(_)` | **error here** — sampling is a statement, handled in story 03 |

`Equals` with more than two operands appears in real code (`4WHS/packages/KX.pkg.ssp`:
`acc1 == acc2 == Some(true)`), so the adjacent-pairs expansion is required, not hypothetical.

### 3.3 Errors

One `EcExportError` enum in `src/writers/easycrypt/mod.rs`, `thiserror` + `miette::Diagnostic`,
carrying the `SourceSpan` the Domino node already has, in the style of
`src/transforms/theorem_transforms.rs`'s error. Variants at least: `UnsupportedType`,
`UnsupportedExpression`, `UnsupportedStatement` (story 03), `PackageTypeParameters` (story 03),
`Name(NameError)`. The message must name the construct and point at the source.

### 3.4 `Types.ec`

Given the theorem and the union of extracted types, emit, in this order and deterministically
(sort by name; never iterate a `HashSet` directly):

```
require import AllCore Distr FMap Int IntDiv.

type bits_n.
op zero_n : bits_n.
op one_n  : bits_n.
op dbits_n : bits_n distr.
axiom dbits_n_ll : is_lossless dbits_n.
…one block per distinct bits type…

op func_prf : bits_n -> (int * int * bits_n * bits_n * bool) -> bits_n.
op func_mac : bits_n -> bits_n -> int -> bits_n.
```

- One block per distinct bits type in the theorem, including `Bits(*)` → `bits` / `zero` / `one` /
  `dbits` / `dbits_ll`.
- One `op func_<name>` per theorem constant of `Fn` type, mirroring Domino's SMT name
  `<<func-{name}>>` (`src/writers/smt/contexts/equivalence/emit.rs:779`). The type is the curried
  arrow built from `Fn(args, ret)`.
- Theorem constants of `Integer` and `Boolean` type are **not** declared here: width integers
  become types, and the rest become lemma binders passed to `Exp.run` (stories 04 and 07).

## 4. Acceptance criteria

- [ ] Unit tests cover every row of both tables in §3.1 and §3.2, including each error row
      asserting an `EcExportError` with a span.
- [ ] `Equals` with three and four operands expands to adjacent-pair conjunctions.
- [ ] `Types.ec` golden files for `example-projects/hello-world` (one identifier width),
      `example-projects/simple-KEM-example` (literal width `bits_256`) and
      `example-projects/4WHS` `Simple4WHS` (`bits_n` plus `func_prf`, `func_mac`) under
      `testdata/easycrypt/story02/`.
- [ ] Each golden `Types.ec` compiles: `easycrypt compile -I <dir> Types.ec` exits 0 (test skips
      when `easycrypt` is absent).
- [ ] Output is deterministic across runs (sorted, no `HashSet` iteration order).
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo test --workspace easycrypt
easycrypt compile -I testdata/easycrypt/story02/4WHS testdata/easycrypt/story02/4WHS/Types.ec
```

## 6. Notes / risks

- **`Maybe(Maybe(T))`** renders as `T option option` — legal, no special case, but keep a test.
- **Do not "helpfully" translate unsupported constructs to something plausible.** A silent wrong
  translation is far worse than a hard error: the generated proof would be about the wrong game.
- **`Bits(*)`** has no width; its constants are `zero`/`one` with no suffix. Watch for collisions
  with a theorem that also has a width literally named nothing — impossible today, but assert.
- The lossless axiom is the only axiom we emit. Do **not** add uniformity/fullness axioms
  speculatively; add them when a proof needs them.

## 7. State handed to the next story

Record in `02-…-IMPLEMENTATION-REPORT.md`: the signature of the type/expression translation entry
points, how the identifier resolver is passed in (story 03 needs to map state fields to module
variables and locals to `var`s), the `EcExportError` variants, the bits-type naming as implemented,
and the golden-file paths.
