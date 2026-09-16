# Story 02 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` and
`cargo clippy --workspace --all-targets` are all clean. `easycrypt` (opam
switch, `r2026.06-12-g7e192dd`) **was available** in this environment, so all
three golden files' compile checks ran for real (not skipped) and passed.

## 1. What exists

`src/writers/easycrypt/types.rs` (type + expression translation) and
`src/writers/easycrypt/typesfile.rs` (the `Types.ec` builder), plus
`EcExportError` in `src/writers/easycrypt/mod.rs`. Unit tests live inline in
each file's own `#[cfg(test)] mod tests` (matching story 01's `names.rs`
precedent, not story 01's separate top-level `tests.rs`, since these tests
are story-02-specific and don't need to share fixtures with the AST/renderer
tests). Golden files and their `easycrypt compile` checks live in
`typesfile.rs`'s test module.

A `#[cfg(test)] pub(crate) mod test_support` was added to `mod.rs`, holding
the "shell out to `easycrypt compile -I dir file`, skip (don't fail) when the
binary isn't on `PATH`" logic that story 01's `tests.rs` had inlined and this
story was about to duplicate a second time. Both `tests.rs` and
`typesfile.rs` now call `test_support::assert_compiles(dir, file)`; later
stories' `*_compiles` tests should use it too instead of re-inlining.

## 2. Entry points (story 03 needs these)

```rust
// types.rs
pub fn translate_type(ty: &Type, span: SourceSpan) -> Result<EcType, EcExportError>;

pub type IdentifierResolver<'a> =
    &'a mut dyn FnMut(&Identifier, SourceSpan) -> Result<EcExpr, EcExportError>;

pub fn translate_expr(
    expr: &Expression,
    span: SourceSpan,
    resolve_identifier: IdentifierResolver,
) -> Result<EcExpr, EcExportError>;

pub fn bits_type_name(count: &CountSpec) -> String;   // "bits_n" / "bits_256" / "bits"
pub fn bits_suffix(count: &CountSpec) -> Option<String>; // "n" / "256" / None
pub fn func_op_name(theorem_const_name: &str) -> String;  // "func_<name>"

// typesfile.rs
pub fn build_types_file(theorem: &Theorem<'_>, types: &HashSet<Type>) -> Result<EcFile, EcExportError>;
```

**Neither `Expression` nor `Type` carries a `SourceSpan` in this codebase**
(`grep SourceSpan src/expressions.rs src/types.rs` — no hits; only
`Statement` and package field declarations, `src/package.rs`'s
`params`/`state: Vec<(String, Type, SourceSpan)>`, have one). So both
`translate_type` and `translate_expr` take `span: SourceSpan` as a caller-
supplied parameter rather than reading it off the node, and echo it back
verbatim in any `EcExportError` they raise. **Story 03 must thread a real
span down** (the statement a translated expression came from, or the
package field declaration a translated type came from) — `translate_expr`
recurses with the same `span` it was given, so one call fixes an entire
sub-tree's errors.

`build_types_file` has no such span to thread at all: `Theorem::consts` and
the `HashSet<Type>` union of `GameInstAux::types` carry no span data
anywhere in the pipeline (`type_extract.rs`'s output is a bare
`HashSet<Type>`). `typesfile.rs::theorem_level_span()` returns a `(0, 0)`
placeholder for this reason. This is a real, documented gap, not a dodge —
nothing reachable from a well-typed theorem's consts/game-instance types can
actually trigger it today, so it wasn't worth plumbing a fake span through
`Theorem`/`GameInstAux` just for this story.

**Identifier resolution** (`Identifier(id)` and `TableAccess`'s table
identifier) is entirely the caller's job via `IdentifierResolver`, a
`&mut dyn FnMut(&Identifier, SourceSpan) -> Result<EcExpr, EcExportError>`.
`translate_expr` calls it and uses the `EcExpr` it returns verbatim (a bare
`EcExpr::Var` for a mangled local, or an `EcExpr::Qualified` for a
module-qualified state field — `translate_expr` doesn't care which). Story
03's resolver will need `Names` state (from `names.rs`) plus a table mapping
package state fields to their module-qualified names; none of that exists
yet, since story 02 had nothing to build it from.

`FnCall(id, args)` does **not** go through the resolver: its identifier is
always a theorem constant (mirrors `src/writers/smt/expr_expr.rs`'s
`id.as_theorem_identifier().unwrap()`), so `translate_expr` calls
`id.as_theorem_identifier().expect(...)` itself and builds
`EcExpr::App { head: func_op_name(name), .. }` directly.

## 3. `EcExportError` (`mod.rs`)

```rust
pub enum EcExportError {
    UnsupportedType { construct: &'static str, span: SourceSpan },
    UnsupportedExpression { construct: &'static str, span: SourceSpan },
    UnsupportedStatement { construct: &'static str, span: SourceSpan },   // unused until story 03
    PackageTypeParameters { span: SourceSpan },                          // unused until story 03
    Name(#[from] NameError),
}
```

`thiserror::Error` + `miette::Diagnostic`, each variant carrying a
`#[label]`ed `SourceSpan`, in the style of `theorem_transforms.rs`'s
`EquivalenceTransformError`. `Name(NameError)` is `#[error(transparent)]`
but **not** `#[diagnostic(transparent)]`: `names::NameError` doesn't itself
implement `Diagnostic` (it has no span data — a `Collision` is between two
raw name strings, not a source location), so the derive falls back to a
diagnostic with no code/label for that variant. `construct` is a
`&'static str` naming the Domino construct (`"List"`, `"Sum"`, `"1-element
Tuple (EasyCrypt has no 1-tuples)"`, …), chosen per match arm — **never**
`Type`'s or `Expression`'s own `Display`/`Debug`, since `Type: Display` has a
`todo!()` fallback for exactly the variants (`List`, `Set`, `AddiGroupEl`,
`MultGroupEl`, `UserDefined`) this error type exists to report, which would
panic while constructing the error.

`PartialEq, Eq` are derived (on top of `Debug, Clone, Error, Diagnostic`) so
tests can `assert_eq!` a whole error value including its span.

## 4. Bits-type naming, as implemented

`bits_type_name`: `Bits(Identifier(id))` → `format!("bits_{suffix}")` where
`suffix = id.as_theorem_identifier().unwrap().ident().replace('-', "_")`;
`Bits(Literal(n))` → `format!("bits_{n}")`; `Bits(Any)` → `"bits"` (no
suffix, ever). Constants (`zero`/`one`/`dbits`/`dbits_ll`) reuse the same
suffix rule. No further mangling (no `d_` prefix, no keyword check) —
Domino width identifiers are always lowercase by construction.

§6's "watch for collisions [with `Bits(*)`'s bare names] ... impossible
today, but assert" is implemented as a `debug_assert!(!suffix.is_empty(),
...)` inside `bits_suffix`'s `Identifier` arm: an identifier-derived suffix
can only be empty if a Domino identifier's name string were empty, which the
parser never produces. `typesfile.rs::collect_bits_types` then keys a
`BTreeMap<String, CountSpec>` by this name directly — two `Type`s that are
structurally different (the same theorem width reached through two
different game instances) but produce the same name collapse to one
`Types.ec` block, correctly, since the name is derived from the underlying
theorem const's identifier.

`func_op_name`: `format!("func_{}", name.replace('-', "_"))`. Never routed
through `Names::mangle` — "func_" is always lowercase, so a `d_` prefix is
never triggered, and two distinct theorem-const names can't collide under
this transform (it doesn't fold case).

## 5. `>`/`>=`, as implemented

Per story 01's inherited note (`02-…md` §2.1): `GreaterThen(a, b)` translates
to `Lt(b, a)` and `GreaterThenEq(a, b)` to `Le(b, a)` — **always flipped**,
never `EcBinop::Gt`/`Ge`. Domino has no `real` type, so every numeric
comparison Domino can produce is over `int`/`Bits`, for which EasyCrypt's
stdlib has no `>`/`>=` at all; the flip is unconditionally correct, so no
local per-type operator override (the story's other option) was needed.

## 6. Golden files

`testdata/easycrypt/story02/{hello-world,simple-KEM-example,4WHS}/Types.ec`,
each generated by loading the named theorem (`Proof` /
`KEM_Proof` / `Simple4WHS`) via `DirectoryFiles`/`DirectoryProject`, running
the real `EquivalenceTransform.transform_theorem`, unioning
`GameInstAux::types` over **all** of `theorem.instances` (not just one
equivalence's two sides — matches §2.4: "unions the sets over all of the
theorem's game instances"), and rendering `build_types_file`'s output. All
three compile under `easycrypt compile -I <dir> Types.ec`. `4WHS/Types.ec`
reproduces the story's own worked example verbatim (`op func_prf : bits_n ->
(int * int * bits_n * bits_n * bool) -> bits_n.` /
`op func_mac : bits_n -> bits_n -> int -> bits_n.`), except `func_mac` is
emitted **before** `func_prf` — `collect_fn_consts` sorts by raw theorem-
const name (`BTreeMap`, never `HashSet` iteration order) for determinism,
and `"mac" < "prf"` alphabetically; the story's own listing was in
`.ssp`-declaration order, not alphabetical, and doesn't mandate one order
over the other.

## 7. Notes for follow-up (not this story's scope)

- `EcExportError::UnsupportedStatement` and `PackageTypeParameters` are
  declared (per §3.3's "variants at least") but unused until story 03.
- Story 03's resolver needs: a `Names` instance seeded with every state
  field/local/const name in a package (to mangle consistently), and a way to
  tell a package-state `PackageIdentifier` from a local/arg one so it can
  return `EcExpr::Qualified` vs `EcExpr::Var`.
- `theorem_level_span()`'s `(0, 0)` placeholder (§2 above) should be
  revisited if a later story makes it reachable from bad input — currently
  nothing in `Theorem::consts`/`GameInstAux::types` can fail translation.
