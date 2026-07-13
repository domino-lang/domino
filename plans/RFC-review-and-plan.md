# RFC Review & Implementation Plan

Review of `plans/RFC.md` against the current codebase, followed by an implementation
plan expressed as user stories.

---

# Part 1 — Issues anticipated

## 1. The headline problem: Domino's expression language cannot express the invariants and randomness mappings we already have

This is the finding that should reshape the RFC. The RFC assumes "Expr" means "a Domino
expression", but the two SMT files it is explicitly trying to replace
(`example-projects/yao/theorem/LayerSecurity/`) use constructs that do not exist
anywhere in `ExpressionKind` ([expressions.rs:435](src/expressions.rs#L435)) or in the
grammar ([ssp.pest:147](src/parser/ssp.pest#L147)):

| Construct | Used in | Exists in Domino? |
|---|---|---|
| `forall` / `exists` | `invariant-Layer.smt2` (2 uses) | **No** |
| `ite` (conditional expr) | `randomness-Layer.smt2` (12 uses) | **No** |
| `=>` (implication) | every `define-lemma` body | **No** |
| `let` | `randomness-Layer.smt2` | **No** (RFC adds it) |
| Negative integer literals | `lemma-*.smt2` (`(= h -2)`) | **No** — `num = ASCII_DIGIT+` |
| Table access on a non-identifier | `(select (maybe-get (select T i)) b)` | **No** — grammar is `identifier ~ "[" ~ expr ~ "]"` |

Without quantifiers and `ite`, the RFC's own motivating case study **cannot be ported**.
The RFC never mentions either. These have to be added to the core expression language
before any of the new blocks are useful, and they are the largest single chunk of work.

The good news: the SMT side already has `SmtForall`, `SmtIte`, `SmtImplies`, `SmtLet`
([writers/smt/exprs.rs](src/writers/smt/exprs.rs)), so lowering is straightforward once
the front-end exists.

## 2. Domino expressions are fully parenthesized — no operator precedence

Every binary operator in the grammar is `"(" ~ expr ~ OP ~ expr ~ ")"`. So the RFC's

```
constraints {
    d > 0 and h > d
}
```

**does not parse.** It must currently be written `((d > 0) and (h > d))`. Every code
sample in the RFC is affected. We need a decision: either accept the parens (and rewrite
the RFC's examples), or introduce a precedence-climbing parser (pest ships `PrattParser`).
I recommend adding precedence — these blocks are prose-like predicates that users will
read far more often than oracle code, and paren soup will hurt adoption. But it is a
change to the shared expression grammar, so it touches package/oracle code too.

## 3. Selector syntax collides with the existing grammar

`left.PackageInstance.Field`, `const.X`, `args.Y`, `left.state.old.P.F`, `left.output`:

- `identifier` does not permit `.`, so these need new rules, ordered **before**
  `identifier` / `fn_call` / `table_access` in the `expression` union (pest is PEG:
  first match wins, so ordering is load-bearing).
- `left`, `right`, `args`, `const` are currently legal identifiers. Making them selector
  heads is a soft reservation; we should decide whether they become reserved words.
- Combining with tables — `left.keys.T[i]` — requires generalizing `table_access`, which
  today only accepts a bare identifier as the base.

There is prior art to reuse: `smtrewrite.rs` already fabricates exactly these
dotted names as SMT `let`-bindings (`gen_pkgbinding`, `gen_varbinding`,
[smtrewrite.rs:60-108](src/gamehops/equivalence/smtrewrite.rs#L60-L108)). The Domino-native
path should share that machinery rather than reimplement it.

## 4. Two identifier namespaces are about to collide

Claim names today are `smt_identifier` (hyphens allowed): `no-abort`, `same-output`,
`equal-aborts`. Domino `identifier` forbids hyphens. The RFC makes lemmata first-class
Domino entities that can be *invoked inside expressions* ("Lemmata can be invoked in other
lemmata") — but `no-abort` inside an expression parses as `no` minus `abort`. And the RFC's
new claim names (`invariant-in-initial-state`, `injective-randomness`) are hyphenated too.
We need to pick one: either lemma names become Domino identifiers (breaking every existing
theorem file), or expression-level lemma invocation uses a distinct syntactic form.

## 5. `ClaimType::guess_from_name` is a landmine

[theorem.rs:209](src/theorem.rs#L209) dispatches on name *prefix*:

```rust
if name.starts_with("relation") { Relation }
else if name.starts_with("invariant") { Invariant }
else { Lemma }
```

and that choice decides the SMT call shape in `emit_claim_assert`
([emit.rs:152-169](src/writers/smt/contexts/equivalence/emit.rs#L152-L169)) —
lemmas get `(old_left, old_right, ret_left, ret_right, args...)`, relations get
`(new_left, new_right)`, invariants get `(new_left, new_right)`.

Consequences for the RFC:
- `invariant Invariant1 { ... }` — capital `I` — is guessed as a **Lemma** and called with
  the wrong arity.
- `injective-randomness` is guessed as a Lemma.
- `invariant-in-initial-state` is guessed as an Invariant.

Name-based guessing has to be replaced by a resolved, typed claim reference. This is a
load-bearing refactor that most of the RFC sits on top of, and it should be done early.

## 6. Invariants are per-oracle in the data model; the RFC makes them per-equivalence

`Equivalence.invariants: Vec<(String /*oracle*/, Vec<String> /*paths*/)>`
([equivalence/mod.rs:28](src/gamehops/equivalence/mod.rs#L28)) and
`EquivalenceContext.invariants: HashMap<oracle, Vec<SmtExpr>>`
([contexts/equivalence.rs:36](src/writers/smt/contexts/equivalence.rs#L36)) are both keyed
by oracle, and the grammar makes `invariant_spec` **mandatory** inside each
`equivalence_oracle`. The RFC's "one set of invariants for the entire hop" inverts this.
Expect a data-model change rippling through `load_invariants`, `append_invariants`,
`emit_invariant`, and the grammar's `equivalence_oracle` rule (which also fixes the order
`randomness? invariant lemmas`).

## 7. Invariants cannot currently be assumed as dependencies

`ClaimType::Invariant => unreachable!()` in the dependency loop
([emit.rs:160](src/writers/smt/contexts/equivalence/emit.rs#L160)). The RFC needs
invariants (and case predicates) usable as *hypotheses*. That `unreachable!()` must go.

## 8. The RFC's per-invariant subclaim formula is wrong as written

RFC lines 80-84 propose checking

```
(=> (invariants old-left old-right) (Invariant1 old-left old-right))
```

`Invariant1` is a conjunct of `invariants`, so this is **trivially valid** and proves
nothing. It should almost certainly be `(Invariant1 new-left new-right)` — assume the
conjunction on the old state, discharge each named invariant on the *new* state. This is
what `build_invariant_new_call` already does. Worth correcting in the RFC before anyone
implements it.

## 9. `invariant-in-initial-state` is new machinery, not new syntax

Nothing today constructs an initial game state. `emit_constant_declarations` declares
`old` and `new` states as free constants and constrains `new` from the oracle function; the
"initial" state (all fields at their init values, sample counters zero) has no term. This
claim also lives at the **equivalence level**, but:
- the grammar has no equivalence-level `claims` block (only `equivalence_oracle`);
- the driver and UI are keyed by oracle (`verify_oracle`, `proofstep_set_oracles`,
  `start_oracle`), and `proof_tree_by_oracle_name` **panics** when an oracle is missing
  ([equivalence/mod.rs:90](src/gamehops/equivalence/mod.rs#L90)).

So this story needs an initial-state term, a grammar addition, and driver/UI changes. It is
the highest-risk item in the RFC and should be scheduled as its own vertical slice.

## 10. Equivalence-wide lemmata must be instantiated per oracle

SMT lemma names are per-oracle: `relation_pattern(name, oracle_name)` produces
`<relation-{name}-{left}-{right}-{oracle}>`, and `handle_define_lemma` even parses the
oracle name back *out* of the function name
([smtrewrite.rs:219](src/gamehops/equivalence/smtrewrite.rs#L219)). "New state" is likewise
per-oracle (`new_global_const_name(game_inst, oracle_name)`). So an equivalence-wide lemma
is really a *template* instantiated once per oracle, not a single SMT function. The RFC
should say so, and we need shadowing rules for when a name is defined both
equivalence-wide and oracle-locally.

## 11. Predicates and functions need a new namespace and topological emission

- Theorem constants of `fn` type are emitted as **uninterpreted** `declare-fun <<func-X>>`
  ([emit.rs:363](src/writers/smt/contexts/equivalence/emit.rs#L363)). User-defined
  predicates/functions are *defined* (`define-fun` with a body). Two different things that
  both look like `Foo(x, y)` at the call site — name collisions need to be rejected.
- "Predicates can be invoked in other predicates" means we need dependency-ordered emission
  plus cycle detection (`SmtDefineFun` has an `is_rec` flag, but we should not allow
  recursion in v1).

## 12. `randomness: all` interacts with a hard-coded assertion

`build_rands` emits `zero_constrain_randctr` — asserting `randctr-{game}-{id} = 0`
unconditionally ([emit.rs:1364](src/writers/smt/contexts/equivalence/emit.rs#L1364)). The
old-state counters are pinned to zero. Before promising `randomness: all`, we should
understand what that assertion is for and whether an all-offsets mapping is meaningful
alongside it.

## 13. There is no typechecker for theorem-level expressions

The `typecheck` transform runs on `Composition`s ([transforms/mod.rs:58](src/transforms/mod.rs#L58)).
Nothing typechecks expressions in a theorem-file context. All the new blocks need a fresh
pass with a scope containing theorem constants, oracle args, instantiated package state
field types, sample ids, and user predicate/function signatures. This is where the RFC's
promised "type checking makes sure `left.id` is asserted to left-game sample ids" actually
lives. Without it, user mistakes surface as raw Z3 sort errors.

## 14. Backwards compatibility

Every example and test project (`yao`, `4WHS`, `kem-dem`, `nprf`, `rosenpass-basic`,
`ae`, plus `test-projects/`) uses the SMT-file path. Both paths must coexist for a long
time. We should decide up front whether SMT files and native blocks may be *mixed* within
one equivalence (I recommend: yes, since the SMT path is just extra `SmtExpr`s prepended).

## 15. Good news worth banking

- **Per-claim parallelism already exists.** `verify_oracle` does `claims.par_iter()`
  ([verify_fn.rs:172](src/gamehops/equivalence/verify_fn.rs#L172)). If named invariants and
  by-cases subgoals are **desugared into ordinary flat `Claim`s** with generated names, the
  RFC's "it would be very useful if these sub claims can be parallelized" comes for free and
  `verify_fn.rs` needs no changes at all. I strongly recommend this desugaring strategy.
- `emit_claim_assert` already hard-codes a single SMT function named `invariant` taking
  `(old_left, old_right)`. The RFC's "generate an `invariants` function that ANDs the named
  ones" maps onto this exactly.

## 16. Answers to the RFC's open questions

- **"Should we allow full Domino statements instead of expressions?"** — Not in v1.
  Statements carry mutation/abort/sampling semantics that have no meaning in a predicate.
  `let ... in` plus `ite` gives the readability win at a fraction of the cost, and lowers
  1:1 to SMT.
- **"Do we have an example that is nicer with a non-Bool function?"** — Yes.
  `randomness-Layer.smt2`'s offset arithmetic (`(* 2 (ite zl 0 1))` repeated 12 times) is
  crying out for an `Int`-returning helper function.
- **"Nested by-cases?" / "per-case lemmata?"** — Both fall out naturally from a desugaring
  implementation, and Yao already needs per-case lemmata (`abort-case-i-is-one`, etc. are
  only meaningful within their case).
- **"Should we allow marking a lemma to be proved only in a specific case?"** — Yes; this is
  what Yao's `abort-case-*` lemmas are emulating by hand today.

---

# Part 2 — Implementation plan (user stories)

Ordered by dependency. Epics 0 and 1 are foundations that nearly everything else needs;
Epic 2 is a deliberately small end-to-end slice to shake out the pipeline early.

## Epic 0 — Expression language foundations

**S0.1 — Operator precedence in expressions**
*As a proof engineer, I want to write `d > 0 and h > d` without nesting parentheses, so
predicates read like the maths they encode.*
- Introduce a Pratt/precedence parser for `expression` in `ssp.pest`.
- Fully-parenthesized input keeps parsing (superset).
- Regression: all existing example and test projects parse unchanged and still verify.
- **Decision required before starting** (see Issue 2) — if we reject this, every RFC example
  needs rewriting instead.

**S0.2 — `let` expressions**
- `let x <- a in Expr` and `let (x, y, z) <- (a, b, c) in Expr`.
- New `ExpressionKind::Let`; lowers to `SmtLet`.
- Scoping + shadowing rules; covered by `walk` / `borrow_map` / `mapfold`.

**S0.3 — Conditional expressions (`ite`)**
- New `ExpressionKind::Ite`; lowers to `SmtIte`.
- Required by `randomness-Layer.smt2`. Blocks Epic 4.

**S0.4 — Implication**
- `=>` operator, `ExpressionKind::Implies`, lowers to `SmtImplies`.

**S0.5 — Quantifiers**
- `forall (i: Integer, b: Bool) . Expr` and `exists`, over explicitly typed binders.
- New `ExpressionKind::Forall` / `Exists`; lowers to `SmtForall` / `SmtExists`.
- Required by `invariant-Layer.smt2`. Blocks Epic 3.

**S0.6 — Expression language gap-fill**
- Negative integer literals.
- Generalize `table_access` so the base may be any expression (`Unwrap(T[i])[b]`).

**S0.7 — Theorem-scope typechecker**
- A typechecking pass for expressions appearing in theorem files, with a scope carrying
  theorem constants, oracle args, instantiated package state field types, and user-defined
  predicate/function signatures.
- Errors are `miette` diagnostics pointing at the source span — never a raw Z3 sort error.

## Epic 1 — Selectors and resolution

**S1.1 — Selector grammar and AST**
- `left.` / `right.` / `const.` / `args.` heads; `.state.old.` / `.state.new.` /
  `.output` paths; ordered ahead of `identifier` in the expression union.
- Decide and document whether these heads become reserved words.

**S1.2 — Selector resolution to SMT terms**
- Resolve selectors against game/package instance state, reusing `gen_pkgbinding` /
  `gen_varbinding` from `smtrewrite.rs` so the SMT-file and Domino-native paths share one
  implementation.
- Unknown package instance / field produces a source-located error.

**S1.3 — Sample-id selectors**
- `left.PkgInst.ORACLE.sample-name` → `(sample-id "PkgInst" "ORACLE" "name")`.
- Validate against `SampleInfo` (`sample_info_left` / `sample_info_right`): a `left.`
  sample id must name a left-game sample. Unknown sample names are a source-located error.

## Epic 2 — `constraints` block *(first end-to-end slice)*

**S2.1 — Theorem-level `constraints { Expr }`**
*As a proof engineer, I want to assume relations over theorem constants without writing an
SMT file.*
- Grammar + AST + `Theorem` field; typechecked as `Bool`.
- Lowered to an `assert` in the equivalence SMT preamble (alongside
  `emit_constant_declarations`).
- Chosen as the first slice because it exercises parse → typecheck → emit end to end while
  touching none of the claim machinery.

## Epic 3 — Invariants in Domino

**S3.1 — Move invariants from oracle scope to equivalence scope**
- `Equivalence.invariants` and `EquivalenceContext.invariants` become equivalence-scoped.
- `equivalence_oracle`'s `invariant_spec` becomes optional.
- Existing SMT-file projects keep verifying (pure refactor; no user-visible change).

**S3.2 — Replace `ClaimType::guess_from_name` with resolved claim references**
- Claims carry a resolved, typed reference instead of a name prefix guess.
- Removes the `ClaimType::Invariant => unreachable!()` restriction so invariants can be
  assumed as dependencies.
- Pure refactor; all existing projects still verify. **Everything below depends on this.**

**S3.3 — `invariant Name { Expr }` blocks**
- Parse named invariants at equivalence level; typecheck as `Bool` in a scope with old/new
  state selectors and `const.`.
- Emit one `<invariant-Name>` `define-fun` per named invariant, plus the conjunction
  `invariant` that `emit_claim_assert` already expects.
- SMT-file invariants continue to work, and may be mixed with native ones.

**S3.4 — Per-invariant subclaims**
- Support Syntax 1 (`invariant: [no-abort]`) and Syntax 2 (`invariant { Inv1: [...] }`).
- Desugar into one flat `Claim` per named invariant, so they parallelize for free.
- Each subclaim discharges `(=> (invariants old) (Inv_i new))` — **note the RFC text says
  `old` here; that is trivially valid and must be `new`** (Issue 8).
- Acceptance: when one named invariant fails, the failure message names *that* invariant.

**S3.5 — `invariant-in-initial-state` claim**
- Construct an initial-game-state term (state fields at init values, counters zero).
- Add an equivalence-level `claims` block to the grammar.
- Extend the driver/UI so a claim can live outside an oracle (today
  `proof_tree_by_oracle_name` panics for unknown oracles).
- Largest risk in the RFC — schedule as its own slice.

## Epic 4 — Randomness mappings in Domino

**S4.1 — `randomness { Expr }`**
- New `RandomnessType` variant carrying an `Expression`.
- Compile to `randomness-mapping-{oracle}` with args
  `(id-0, id-1, offset-0, offset-1)`; `left.id`/`right.id` → `id-0`/`id-1`,
  `left.ctr`/`right.ctr` → `offset-0`/`offset-1`.
- Body may reference global constants (old state, oracle args, theorem constants) — these
  are already emitted before the per-oracle SMT, so ordering works.
- Depends on S0.3 (`ite`) and S1.3 (sample ids).
- Acceptance: `randomness-Layer.smt2` is expressible natively and Yao's `LayerSecurity`
  still verifies.

**S4.2 — `injective-randomness` claim**
- Generate the injectivity proof obligation over the mapping relation.

**S4.3 — Investigate `randomness: all`** *(spike)*
- Determine what `zero_constrain_randctr` (Issue 12) is enforcing and whether an
  all-offsets mapping is sound and useful alongside it. Answer the RFC's open question
  before committing to the feature.

## Epic 5 — Lemmata, predicates, functions

**S5.1 — Oracle-specific lemmata**
- `lemma Name { Expr }` inside an oracle block; scope includes `args.`, `left.output`,
  old/new state, `const.`.
- Emit as `<relation-{name}-{L}-{R}-{oracle}>`, matching the existing SMT convention.

**S5.2 — Equivalence-wide lemmata**
- Instantiated once per oracle (Issue 10); scope restricted to old/new state and `const.`.
- Define shadowing rules against oracle-local names.

**S5.3 — Predicates (argument-free and with arguments)**
- Equivalence-wide and oracle-specific; invocable from invariants, lemmata, and other
  predicates.
- Enforce: equivalence-wide predicates that read new state may not be used in invariants.
- Topologically ordered emission with cycle detection; reject collisions with `fn`-typed
  theorem constants (Issue 11).

**S5.4 — Functions (non-Bool return)**
- Same as S5.3 with a declared return type.
- Motivating case: the offset arithmetic in Yao's randomness mapping.

## Epic 6 — Proving by cases

**S6.1 — `by cases` desugaring**
- `Claim requires [...] by cases { case1: [...] ... }`.
- Desugar into flat `Claim`s: one comprehensiveness claim
  (`invariants ∧ randomness ∧ required ⟹ ⋁ cases`) plus one claim per case
  (`... ∧ case_i ∧ case-lemmata ⟹ goal`).
- Desugaring keeps `verify_fn.rs` untouched and gives per-case parallelism for free.

**S6.2 — Per-case lemmata and nesting**
- Per-case `requires`/lemma blocks (RFC Q1) — Yao's `abort-case-*` lemmas need this.
- Nested `by cases` (RFC Q2) falls out of the recursive desugaring.
- Case-scoped lemma marking (RFC Q3).

## Epic 7 — Migration and hardening

**S7.1 — Port `LayerSecurity` to native Domino as the acceptance test**
- `invariant-Layer.smt2` and `randomness-Layer.smt2` are replaced by native blocks and the
  proof still verifies. This is the real definition of done for the RFC.

**S7.2 — Port `HybridSecurity` including its hand-rolled case split**
- Its `case-i-is-*` / `abort-case-i-*` lemmas become a real `by cases`.

**S7.3 — Diagnostics and documentation**
- Source-located `miette` errors for every new construct.
- Document the new blocks and the (still supported) SMT escape hatch.

---

## Suggested sequencing

1. **Decide S0.1** (operator precedence) — it changes the shape of every example in the RFC.
2. **Correct the RFC** on Issue 8 (`old` vs `new` in per-invariant subclaims).
3. Epic 0 → Epic 1 → **Epic 2 as the first vertical slice**.
4. **S3.2** (kill `guess_from_name`) as early as possible — it is the chokepoint the rest of
   the claim work depends on.
5. Then Epics 3–6, with S3.5 (`invariant-in-initial-state`) treated as an independent,
   higher-risk slice.
