# Story 03 — Package variants: modules, state, oracles, abort

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 01 (AST/renderer/names), story 02 (types, expressions, errors).
**Blocks:** 04, 08.

---

## 1. Why this story exists

This is the heart of the export: turning a Domino package into an EasyCrypt module whose procedures
have Domino's abort semantics without Domino's abort statement.

## 2. Inherited from earlier stories

### 2.1 From 01 and 02

The AST, the renderer, `Names::mangle` (uppercase-first and keywords get `d_`; `ec_` is reserved
for generated names), the type/expression translation and `EcExportError`.

### 2.2 The pipeline has already run (overview §8.2)

Export runs `EquivalenceTransform` (`run_treeify = true`). By the time you see a package:

- `deconstructinvoke` has split tuple-destructuring invokes, `unwrapify` has hoisted `Unwrap` out
  of expressions into their own statements, `resolveoracles` has attached an `Edge` to every
  invoke, `loopunroll` has unrolled bounded `for`s (an unbounded one has already errored),
  `returnify` guarantees every path ends in a `return`, `treeify` has pushed the continuation of
  every `if` into both branches, and `tableinitialize` has inserted `<gen> <- empty` before the
  first write to each compiler-generated **local** table (never package state).
- **Every instance is monomorphic**: `PackageInstance.pkg` is already rewritten with all types and
  parameters substituted (`src/packageinstance.rs:31`).

### 2.3 Shapes you will match on

```rust
// src/statement.rs
enum Statement { Abort(SourceSpan), Return(Option<Expression>, SourceSpan),
                 Assignment(Assignment, SourceSpan), InvokeOracle(InvokeOracle),
                 IfThenElse(IfThenElse), For(..) }
struct Assignment { pattern: Pattern, rhs: AssignmentRhs }     // fields are pub(crate) — fine, same crate
enum Pattern { Ident(Identifier), Table { ident, index }, Tuple(Vec<Identifier>) }
enum AssignmentRhs { Expression(Expression),
                     Sample { ty, sample_name, sample_id },
                     Invoke { oracle_name, args, edge, return_type } }
struct InvokeOracle { oracle_name, args, edge, file_pos }
// src/package.rs
struct OracleSig { name: String, args: Vec<(String, Type)>, ty: Type }
struct OracleDef { sig: OracleSig, code: CodeBlock, file_pos: SourceSpan }
struct Package { name, types: Vec<String>, params: Vec<(String, Type, SourceSpan)>,
                 state: Vec<(String, Type, SourceSpan)>, oracles, imports: Vec<(OracleSig, _)>, .. }
struct PackageInstance { name, params: Vec<(PackageConstIdentifier, Expression)>,
                         types: Vec<(String, Type)>, pkg: Package }
```

There is **no `Assert` statement** — Domino's `assert e` is parsed into an `IfThenElse` whose
else-branch aborts. `treeify` therefore already handled asserts; you do not special-case them.

## 3. Work to do

New file `src/writers/easycrypt/package.rs`.

### 3.1 Package variants

A **variant** is a package specialised to one parameter assignment. Compute its key from a
`PackageInstance`:

```
key = (pkg.name,
       [ (param_name, expr) for params of type Integer ]   // ordered by declaration
       [ (param_name, expr) for params of type Fn ],
       import_grouping)
```

- Boolean parameters are **not** in the key — they are `init` arguments.
- `import_grouping` is the ordered list of `(callee variant name, [imported oracle names])` taken
  from the composition's `edges` where `edge.from()` is this instance. It is part of the key
  because it determines the functor's parameter list. Two instances of one package wired to
  differently-shaped callees are different variants. None of `4WHS`, `hello-world`,
  `simple-KEM-example` or `kem-dem` splits this way, but the key must be honest.
- A `PackageInstance` with a non-empty `types` (Domino package **type parameters**) is a hard
  error `EcExportError::PackageTypeParameters`. Only `nprf` uses them, and it is not a target.

**Naming**: if a package has exactly one variant in the theorem, the module and file keep the
package's name (`KX.ec`, `module KX`). With several, they become `KX_v1`, `KX_v2`, … in first-use
order — first use meaning the order game instances appear in the theorem, then the composition's
`ordered_pkgs_idx()`. Each file opens with a comment naming the assignment:
`(* KX_v2: n = n, prf = func_prf *)`.

### 3.2 The module

One file per variant, `packages/<Variant>.ec`:

```
require import AllCore Distr FMap Int IntDiv Types.
require Interfaces.       (* story 04 owns Interfaces.ec; requiring it here is fine *)

module KX (P_Prot : Interfaces.Prot_i) (P_PRF : Interfaces.PRF_i) = {
  var d_LTK : (int, bits_n) fmap
  var d_H   : (int, bool) fmap
  var b     : bool                (* boolean package parameter *)

  proc init(b_ : bool) : unit = { d_LTK <- empty; d_H <- empty; b <- b_; }

  proc d_NewKey(ltk : bits_n option) : int option = { … }
}.
```

- **State fields become module variables**, names mangled. Non-Bits-width integer parameters and
  boolean parameters become module variables too.
- **Functor parameters**: one per callee instance in `import_grouping`, named `P_<calleeInst>`,
  typed with the callee's module type from `Interfaces` (story 04 emits those; agree the naming
  `<Variant>_i` with it and record it).
- **`init`** takes the boolean and value-integer parameters in declaration order and assigns:
  every state field to `Type::default_expression` (`src/types.rs:210` — `0`, `false`, `None`,
  `empty`, tuple-of-defaults, bits literal `0` → `zero_n`), then each parameter variable from its
  argument. A package with no state and no such parameters gets **no** `init`.
- Do **not** give the module an `implements` clause: story 04 decides whether routers/interfaces
  need it. (EasyCrypt checks module types structurally.)

### 3.3 Oracles and abort — the core rule

An oracle returning `T` becomes `proc <name>(args) : T option`, and one returning nothing becomes
`: unit option`. The body uses a single result variable and a single `return`:

```
proc d_Send1(ctr : int) : bits_n option = {
  var ec_result : bits_n option <- None;
  …
  return ec_result;
}
```

Translation per statement:

| Domino | EasyCrypt |
|---|---|
| `Return(Some e)` | `ec_result <- Some <e>;` |
| `Return(None)` (empty return type) | `ec_result <- Some tt;` |
| `Abort` | *nothing* — `ec_result` is already `None` |
| `Assignment(Ident, Expression)` | `x <- e;` (declare `x` in `locals`) |
| `Assignment(Table{ident,index}, Expression)` | see §3.4 |
| `Assignment(Tuple, Expression)` | `(a, b) <- e;` |
| `Assignment(_, Sample{ty, …})` | `x <$ dbits_n;` — `ty` must be `Bits`, else hard error |
| `IfThenElse` | `if (c) { … } else { … }` — no nesting needed, `treeify` already duplicated the continuation |
| `Assignment(_, Invoke{…})` / `InvokeOracle` | see §3.5 |
| `Unwrap` statement (from `unwrapify`) | see §3.5 |
| `For` | hard error — `loopunroll` leaves only unbounded loops |

### 3.4 Table writes

`T[k] <- rhs` where `rhs : Maybe(V)`:

- `Some e` → `T.[k] <- e;`
- `None` → `T <- rem T k;`
- anything else → `T <- if <rhs> = None then rem T k else T.[k <- oget <rhs>];`

The same applies to generated local tables; their `<gen> <- empty` from `tableinitialize` becomes
a local `var` plus `g <- empty;`.

### 3.5 Continuation nesting (the part `treeify` does **not** do)

> **Superseded by story 16.** `easycryptify` replaced `treeify` in the export pipeline and now
> generates these guards itself, so the writer no longer nests continuations and no longer emits an
> empty `then` branch. §3.5 and the first two bullets of §6 below describe the behaviour as it was
> implemented in this story; read `16-easycryptify.md` for what the writer does now.

`treeify` only duplicates after an `if`. Two statement kinds abort *without* being an `if`, and for
those the translator nests the **rest of the block** into the `else` branch itself:

**Unwrap** (`x <- Unwrap(e)` as its own statement after `unwrapify`):

```
if (<e> = None) {
} else {
  x <- oget <e>;
  …rest of the block, translated…
}
```

**Invoke** (`y <- invoke O(args)` / bare `invoke O(args)`), where the callee's EasyCrypt procedure
returns an option and `None` means it aborted:

```
ec_r0 <@ P_Prot.d_Run1(<args>);
if (ec_r0 = None) {
} else {
  y <- oget ec_r0;
  …rest of the block, translated…
}
```

Generated temporaries are `ec_r<N>`, numbered per procedure. The empty `then` branch is
deliberate: `ec_result` stays `None`, which *is* the abort. Render it as `if (…) {` `} else {`
with an empty then-block rather than inverting the condition, so the shape matches Domino's
"abort here" reading and story 08's listing lines up with it.

A bare `InvokeOracle` statement (return value discarded) binds to a temporary and nests the same
way — the abort still has to propagate.

### 3.6 Locals

Collect every assigned identifier that is not a state field into `EcProc::locals` with its type,
declared in first-assignment order. Oracle arguments are procedure parameters, not locals.

## 4. Acceptance criteria

- [ ] `hello-world`'s two packages export; `fwd` and `fwd2` produce **one** variant (identical
      parameters), proving dedup works.
- [ ] `4WHS` `Simple4WHS` packages export; golden files under `testdata/easycrypt/story03/`.
- [ ] Golden test for each of: a table write with `Some`, with `None`, and with a general `Maybe`
      expression; an `Unwrap` with two following statements (both must land inside the `else`); an
      invoke with following statements; a sample; an `assert` (must come out as a plain `if`, since
      `treeify` handled it).
- [ ] An oracle with no return type produces `: unit option` and `Some tt`.
- [ ] A package instance with a `types { … }` block errors with `PackageTypeParameters`; a `For`
      that survived `loopunroll` errors; sampling a non-`Bits` type errors. All with spans.
- [ ] Every generated package file compiles once story 04's `Interfaces.ec` exists — in this story,
      compile the ones without imported oracles (`4WHS`'s `Prot`, `PRF`) standalone.
- [ ] Deterministic output; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo test --workspace easycrypt
# eyeball against the manual translation — inspiration only, never copy:
#   ~/Research/ec4whs/simple/KX.ec, Prf.ec
```

Never run `domino prove`/`debug` on 4WHS. Export/`cargo test` is fine.

## 6. Notes / risks

- **The empty `then` branch is not dead code.** Removing it (by inverting the condition) changes
  which line the debugger reports as the abort point in story 08. Keep it.
- **`treeify` blow-up is expected.** The generated bodies are deeply nested and repetitive; that is
  the accepted cost of EasyCrypt's single-return rule (overview §3). Do not "optimise" by
  re-flattening — story 08's labels depend on this shape.
- **`ec_result` never gets re-read.** It is written on return paths only, so no path can observe a
  stale value.
- **Watch state-vs-local shadowing**: a Domino oracle local with the same name as a state field
  must not silently alias the module variable. Resolve identifiers through the resolver from story
  02 and add a test.

## 7. State handed to the next story

Record in `03-…-IMPLEMENTATION-REPORT.md`: the variant key and naming as implemented, the module
type naming convention you agreed for functor parameters (story 04 must match), the temporary
naming (`ec_r<N>`, `ec_result`), the `init` signature rule, the continuation-nesting shape, and the
golden-file paths.
