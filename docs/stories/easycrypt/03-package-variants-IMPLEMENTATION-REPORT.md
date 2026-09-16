# Story 03 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (267 passed, 4 pre-existing
`#[ignore]`d, none new) and `cargo clippy --workspace --all-targets` are all clean. `easycrypt`
(`r2026.06-12-g7e192dd`) was on `PATH`, so every `*_compiles` test ran for real.

## 1. What exists

`src/writers/easycrypt/package.rs` (~1290 lines), registered as `pub mod package;` in
`src/writers/easycrypt/mod.rs`. Two small, necessary corrections landed in story 02's
`src/writers/easycrypt/types.rs` — see §6. Tests are inline (`#[cfg(test)] mod tests` at the
bottom of `package.rs`), following `types.rs`'s precedent, not story 01's separate `tests.rs`.

Public entry point:

```rust
pub struct PackageVariant { pub name: String, pub file: EcFile }
pub fn compute_package_variants(theorem: &Theorem<'_>) -> Result<Vec<PackageVariant>, EcExportError>;
```

Story 04 calls this once per theorem and gets back every distinct package variant, deduplicated
and named, in deterministic first-discovery order, ready to render to `packages/<name>.ec`.

## 2. Variant keys and naming, as implemented

`VariantKey { pkg_name, int_params: Vec<(String, ParamValue)>, fn_params: Vec<(String, ParamValue)>,
imports: Vec<(Vec<String>, Box<VariantKey>)> }`, exactly the shape in §3.1: boolean params excluded,
int/fn params ordered by the package's own declaration order (`pkg.params`, not
`PackageInstance.params`'s possibly-different order), `imports` grouped by callee in first-edge
order.

**The non-obvious part**: an int/fn param's *assigned expression* is not directly comparable across
game instances. `Real`/`Ideal`/`Hybrid0` in `Simple4WHS` all instantiate the same `Hybrid0`
composition, but `theorem.rs`'s per-game-instance rewrite (`InstantiationContext::rewrite_pkg_inst`)
tags every `GameIdentifier`/`PackageIdentifier` it touches with that specific game instance's
`game_inst_name` — so the *same* theorem constant `n`, reached through three different game
instances of the same composition, produces three structurally-different `Expression`s (differing
only in that tag). Naively comparing `Expression`s would have split `KX`/`Prot` into one variant per
game instance, breaking dedup entirely. `canonical_param_value` (package.rs:75) fixes this by
resolving through `Identifier::as_theorem_identifier()` first — which already walks past exactly
that instance-specific tagging down to the bare `TheoremIdentifier::Const` — and only falls back to
raw `Expression` equality for a genuine literal (which carries no such tag). `imports` avoids the
same problem structurally: it embeds the *callee's own recursively-computed key* rather than a name,
so no name has to be resolved (and no instance-tag stripped) before two callers' keys can be compared
for equality.

**Naming** (`assign_names`, package.rs:167): group discovered keys by `pkg_name` in discovery order
(`theorem.instances` order, then `ordered_pkgs_idx()` within each composition, per §3.1); one key per
package name gets the bare mangled package name, more than one gets `_v1`, `_v2`, ... in that
discovery order.

**Discrepancy found against the story's own worked example** — flagged during code review and
re-verified independently, kept as designed rather than "fixed" to match the acceptance bullet: §4
says "`fwd` and `fwd2` produce **one** variant (identical parameters), proving dedup works", and §3.1
separately claims "None of `4WHS`, `hello-world`, ... splits [via import_grouping]". Both are
contradicted by `hello-world/games/BigComposition.comp.ssp`: `fwd`'s `UsefulOracle` is served by
`rand` (Rand-shaped), `fwd2`'s by `fwd` (Fwd-shaped) — two *differently-shaped callees*, which is
exactly the case §3.1 itself says must NOT share a variant ("Two instances of one package wired to
differently-shaped callees are different variants"). The implementation follows that more carefully
reasoned rule: `fwd` and `fwd2` render as `Fwd_v1`/`Fwd_v2`, not one `Fwd`. What the acceptance bullet
was actually gesturing at — real dedup, not "same instance count" — does hold:
`medium_composition`'s `fwd`, `medium_composition_more_oracles`'s `fwd` and `big_composition`'s `fwd`
(all three wired to a Rand-shaped callee) all collapse into the single `Fwd_v1` key; only `fwd2`
(wired to a Fwd-shaped callee) is the odd one out. Proven by
`hello_world_fwd_shares_a_key_across_compositions_but_not_with_fwd2`
(package.rs test module). **Story 04 and later stories should expect three hello-world `Proof`
variants (`Rand`, `Fwd_v1`, `Fwd_v2`), not two.**

## 3. The module, as implemented

State fields become module `var`s in declaration order (`Names::mangle(NameKind::Var, ..)`, shared
per-package registry — see §5). A package param becomes a module `var` too iff it's `Boolean`, or
it's `Integer` and **never used as a `Bits` width anywhere in the package** — checked by
`integer_param_used_as_width` (package.rs:257), which walks state field types, every oracle
signature, and every `Type` embedded in oracle code (`Sample`/`BitsLiteral`/`EmptyTable`/`None`
expressions, recursively). This is a heuristic, not something the story states outright as an
algorithm — flagged as such (a "Repeated Switches" risk: this exhaustively matches
`ExpressionKind`/`TypeKind`/`Statement` the same way `types.rs` does, for a different purpose, so a
new Domino AST variant needs updating in both places to stay correct) but it's the only thing that
can be checked structurally, and it correctly identifies `n` (width-only, no var) vs `b` (boolean,
gets a var) in `KX`/`PRF`/`Prot`.

`init` (package.rs:451): boolean/value-int params as args (`<mangled>_` names, e.g. `init(b_ : bool)`
— matches the story's own worked example), body assigns every state field its
`Type::default_expression()` (translated via `translate_expr` with an `unreachable!` resolver, since
a default expression never contains an `Identifier` — checked by construction against
`Type::default_expression`'s own match arms), then each param var from its arg. No `init` proc at all
if there's neither state nor a param-var (§3.2's rule): `Prot` has neither state nor a value param
(its only param, `n`, is width-only) and gets no `init` proc at all; `PRF` has state and gets one —
see the golden files.

**Functor params**: `P_<mangled-callee-instance-name>`, one per distinct callee in edge order, typed
`Interfaces.<callee-variant-name>_i`. **Agreement for story 04**: the module-type name is
`<PackageVariantName>_i` in the `Interfaces` theory/file — e.g. `KX`'s sole functor param is
`(P_Prot : Interfaces.Prot_i)`. Story 04 must emit exactly one `module type <Variant>_i` per package
variant this story produces, named this way.

`Do not give the module an implements clause` — followed literally; `EcModule.implements` is always
`None` here.

## 4. Oracles and abort, as implemented

Every oracle proc: `var ec_result : T option <- None<:T>;` first, `return ec_result;` last, uniformly
— `T` is `unit` (from `Type::empty()`) when the Domino oracle has no return type, giving
`unit option` / `Some tt` exactly as required. Locals are collected in a separate pre-pass
(`collect_locals`, package.rs:530) over the *raw* Domino statement tree (walking both branches of
every `IfThenElse`, deduplicating by raw name so a variable reassigned across branches or oracles
isn't redeclared), before the actual per-statement translation runs — declaration order therefore
matches first-assignment order exactly as the story requires. Table-pattern targets contribute no
new local of their own (§3.4/§3.6 note): a generated local table's own `<gen> <- empty;`
(`tableinitialize`'s insertion) is itself an `Ident`-pattern assignment, so it's already covered by
the same pass — no separate case was needed.

**A real bug found by compiling, not by re-reading the spec**: the first draft never declared the
`ec_r<N>` temporaries `translate_invoke`/table-pattern-sample introduce — EasyCrypt requires every
proc-local (including these) to have an explicit `var`, so the generated `KX.ec` failed to compile.
Fixed by having `OracleTranslator` track `temp_decls: Vec<(String, EcType)>`, populated by a single
`declare_temp(ty)` entry point (replacing the original `next_temp() -> String`), appended to
`EcProc::locals` after body translation. Confirmed by compiling the fixed output.

**Continuation nesting** (§3.5) is implemented as: `Return`/`Abort` end the current
`translate_block` call immediately, returning what's been built so far and *discarding* whatever
(syntactically) follows in that slice; `Unwrap` (an `Ident`-pattern assignment whose RHS is
`ExpressionKind::Unwrap`) and `Invoke`/`InvokeOracle` recursively translate the *rest of the
statement slice* into the `else` branch of a freshly built `if`, then also return immediately. The
"discard what follows a Return/Abort" half of this is not explicitly spelled out in the story, but is
load-bearing and was found empirically: `treeify` blindly appends the continuation of the *first* `if`
it finds in a block onto **both** of that if's branches, even when a branch already ends in an
explicit `return` (a mid-block `if` whose `then` returns early but has no `else`, e.g.
`PRF.pkg.ssp`'s `Eval` oracle) or already ends in `Abort` (an `assert`'s `else`). The result is
syntactically-real-but-semantically-dead statements *after* an already-terminal `Return`/`Abort` in
the raw Domino tree reaching this story's translator. Translating them anyway would silently
overwrite `ec_result` after it was already set. Stopping at the first `Return`/`Abort` is therefore
not an optimisation — it's required for correctness, and it was only caught by compiling `4WHS`
end-to-end (see §7).

Table writes (§3.4): `Some(e)` → `T.[k] <- e;`; `None` → `T <- rem T k;` (both confirmed compiling in
the goldens/tests); the general `Maybe` fallback duplicates the (pure, side-effect-free) expression
three times as specified, confirmed live in `KX.ec`'s `NewKey`/`NewSession` (`LTK[kid_] <- ltk;`,
`Fresh[ctr_] <- H[kid];`). A table-pattern `Sample`/`Invoke` (not shown in any of this story's target
projects, but syntactically legal Domino) is handled by sampling/calling into a fresh `ec_r<N>` first,
then doing the same `Some(...)`-write; untested against `easycrypt compile` since no example project
exercises it.

## 5. Naming/collision-registry discipline

One `PackageScope { names: Names, functor_params: HashMap<usize, String> }` per rendered variant,
`names` seeded with state fields then param-vars, then reused (same `NameKind::Var` namespace) for
every oracle's args and locals — deliberately, so a state field and an unrelated local/arg that
happen to share a raw name resolve to the *same* mangled name only when they're genuinely the same
Domino identifier (impossible for Domino's own resolver to produce a false positive here, since
`PackageIdentifier::State` vs `::Local`/`::OracleArg` is decided once, upstream, by static scope
resolution — a state field reference is never re-resolved as a fresh local of the same name).

Two places reference *another* package's naming and could not reuse this registry:
`build_functor_params` needs one dedicated, call-scoped `Names` (package.rs, `functor_names`) shared
across all of one module's functor params, so two differently-named callee instances that happened
to mangle to the same `P_<...>` would be caught as a hard collision instead of silently colliding
(fixed after code review flagged the original `Names::new()`-per-iteration version as defeating this
exact guarantee); `translate_invoke`'s callee-proc-name lookup legitimately uses a fresh `Names::new()`
per call — it reproduces the callee's own `Proc`-namespace mangling of one already-known name, and
that namespace's collision-freedom was already validated when the callee itself was rendered (a
callee is always discovered, and therefore rendered, before its caller — see §2's discovery order —
so `compute_package_variants` would already have propagated a `NameError::Collision` from the
callee's own `build_proc` before this call site is ever reached).

## 6. Corrections to story 02's `types.rs`

Found while exporting `4WHS/packages/Prot.pkg.ssp`, which uses `(Bits(n))`-style parenthesisation as
a return-type grouping (`Run1(...) -> ((...11-tuple...), (Bits(n)))`). Story 02 recorded (and tested)
that a 1-element Domino `Tuple` "cannot occur — ... Domino's own parser never produces one". False:
`type_tuple = { "(" ~ tipe ~ ( "," ~ tipe )* ~ ")" }` (`src/parser/ssp.pest:133`, and identically for
expressions at `:234`) makes the repetition optional, so a single parenthesised type or expression —
used throughout `Prot.pkg.ssp` and `PRF.pkg.ssp`'s Run/Send oracles — parses as a genuine 1-element
`Tuple`. `translate_type`/`translate_expr` now elide a 1-element `Tuple` to its single element instead
of hard-erroring (both changes are two-line, narrowly scoped, with the story-02 test renamed and
updated in place, and the old wrong claim replaced with a doc comment citing the exact grammar rule
and file). This was necessary, not optional, for this story's own acceptance criteria (4WHS exporting
at all) — every `Prot`/`KX`/`PRF` oracle whose return type or return expression uses this idiom would
otherwise hard-error.

## 7. Golden files / compile checks

`testdata/easycrypt/story03/{hello-world,4WHS}/*.ec`, generated from the real projects (`Proof` /
`Simple4WHS`) through the real `EquivalenceTransform` pipeline, same pattern as story 02's
`typesfile.rs` tests. Also committed: `Types.ec` in each directory (needed as an `-I` companion for
`easycrypt compile`, built via story 02's `build_types_file`, not part of this story's own output).

- `hello-world`: `Rand.ec`, `Fwd_v1.ec`, `Fwd_v2.ec` (see §2 for why three, not two). `Rand.ec`
  compiles standalone (no imports); `Fwd_v1`/`Fwd_v2` need `Interfaces.ec` (story 04), golden-text-only
  here.
- `4WHS` (`Simple4WHS`, the full theorem — all ten `instance`s, six underlying compositions): seven
  variants, each package appearing exactly once (`Prot`, `KX`, `Prot_NoKey`, `KX_NoKeys`, `PRF`,
  `Prot_NoPrf`, `KX_NoPrf`) — confirming `Real`/`Ideal`/`Hybrid0`'s shared boolean `b` correctly does
  *not* split `KX` three ways. `Prot.ec` and `PRF.ec` (no imports) compile standalone, matching the
  acceptance criterion exactly; every other variant here imports at least one oracle and needs
  `Interfaces.ec`.

Unit tests (hand-built minimal fixtures, `package.rs`'s own `mod tests`) cover what the real projects
don't exercise: a bare-`None` table write (flagged missing by code review — none of `4WHS`/
`hello-world`'s table writes use a literal `None`, only `Some`/general-`Maybe`), the no-return-type
→ `unit option`/`Some tt` case, and the three hard errors (`PackageTypeParameters`, a surviving `For`,
sampling a non-`Bits` type) — plus two hand-built variant-key tests (`distinct_int_param_literals_...`,
`identical_int_param_literals_...`) isolating the naming logic from a real project's parsing cost.

## 8. State handed to the next story

- **Entry point**: `compute_package_variants(theorem: &Theorem<'_>) -> Result<Vec<PackageVariant>, EcExportError>`,
  `PackageVariant { name: String, file: EcFile }`, one per distinct variant, deterministic order.
- **Variant naming**: bare mangled package name if unique in the theorem, else `_v1`/`_v2`/... in
  discovery order (theorem-instance order, then `ordered_pkgs_idx()`). **hello-world's `Proof` yields
  three variants, not two** (§2) — update any assumption downstream expecting `fwd`/`fwd2` to share a
  module.
- **Module-type naming for story 04**: `<PackageVariantName>_i`, e.g. `Prot_i`, `KX_v2_i`. Every
  functor parameter this story emits is already typed `Interfaces.<callee-variant>_i` expecting this.
- **Temporaries**: `ec_result` (always present, first local), `ec_r<N>` (1-indexed per proc, always
  declared as a local of the right type — `T option` for an invoke result, `T` for a table-pattern
  sample).
- **`init` signature**: boolean/value-integer params only, in package declaration order, arg names
  `<mangled-var-name>_`; absent entirely when the package has neither state nor such a param.
- **Continuation-nesting shape**: `if (<abort-check>) { } else { <rest> }`, empty `then` always —
  never invert the condition (debugger line-labelling in story 08 depends on this, per the story's own
  §6 note, and now also because of §4's dead-code-after-return discovery: the *documented*
  Return/Abort-terminates-the-block behavior of this translator is not just cosmetic).
- **Golden-file paths**: `testdata/easycrypt/story03/{hello-world,4WHS}/*.ec`.
- Boolean/value-integer param-vars vs Bits-width-only params: decided by
  `integer_param_used_as_width` (§3) — a real heuristic, not a lookup table; if a later story adds a
  new place a `Type` can embed a `CountSpec::Identifier` (a new `ExpressionKind`/`Statement` variant),
  this function needs updating too, silently (no compiler-enforced exhaustiveness, since it has `_ =>
  false` fallbacks for lookup convenience).

## 9. Notes for follow-up (not this story's scope)

- Table-pattern `Sample`/`Invoke` (§4 of this report) are implemented but never exercised against
  `easycrypt compile` — no example project uses them. Worth a targeted test once a project surfaces
  one, or before relying on it for a real proof.
- `PackageTypeParameters`'s span, like `typesfile.rs`'s `theorem_level_span()`, falls back through
  "first state field, else first oracle, else `(0,0)`" since `PackageInstance::types` carries no
  `SourceSpan` in Domino's data model. Real for well-typed input from every target project (`nprf` is
  the only project using package type params and isn't a target), documented at the call site.
