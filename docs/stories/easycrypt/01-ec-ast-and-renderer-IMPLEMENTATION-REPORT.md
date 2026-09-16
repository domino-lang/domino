# Story 01 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` and
`cargo clippy --workspace --all-targets` are all clean. `easycrypt` (opam
switch, `r2026.06-12-g7e192dd`-equivalent build under
`~/.opam/easycrypt/bin/easycrypt`) **was available** in this environment, so
the golden file's compile check actually ran (not skipped) and passed.

## 1. What exists

`src/writers/easycrypt/{mod,ast,names,render}.rs`, registered as `pub mod
easycrypt;` in `src/writers/mod.rs` (the only change outside the new
directory). Tests live in `src/writers/easycrypt/tests.rs` (`mod tests;`
under `#[cfg(test)]` in `mod.rs`), plus unit tests inline in `names.rs`.

Fixtures: `testdata/easycrypt/story01/kitchen-sink.ec` (the golden file) and
`testdata/easycrypt/story01/Base.ec`, a small hand-written theory
(`type t. op dummy : int.`) that the kitchen sink `require import`s and
`clone`s — needed because `ast.rs` has no `theory ... end` item (out of
scope for this story), so `Clone` needs a base theory that already exists as
its own file.

## 2. `ast.rs` — final variant list

Implemented **exactly** as specified in the story, with derives
(`Debug, Clone, PartialEq`, plus `Copy, Eq` on the plain-enum types) and the
doc comments from the story carried over. No variants were added or removed.
Every `EcItem`, `EcStmt`, `EcLvalue`, `EcExpr`, `EcUnop`, `EcBinop`,
`Quantifier`, `EcType`, `CloneOverride`, `LemmaBinder` variant is exercised
in the kitchen-sink golden file (see the file itself, or
`tests.rs::kitchen_sink` for the AST that produces it).

**No `Raw` variant anywhere; `EcLemma::proof` is still the only place raw
text is allowed**, as required.

## 3. `render.rs` — precedence table as implemented

Loosest to tightest, with the precedence level used internally (not
EasyCrypt's own numeric levels, just this renderer's relative ordering):

| Level | Operators | Assoc |
|---|---|---|
| 0 | `=>` (`Implies`); also `if`/`let`/`forall`/`exists` (always parenthesised as an operand unless at true top level) | right |
| 1 | `\/` (`Or`) | left |
| 2 | `/\` (`And`) | left |
| 3 | `=` `<>` (`Eq`, `Ne`) | left |
| 4 | `<` `<=` `>` `>=` (`Lt`, `Le`, `Gt`, `Ge`) | left |
| 5 | `+` `-` (`Add`, `Sub`) | left |
| 6 | `*` `%/` `%%` (`Mul`, `Div`, `Mod`) | left |
| 7 | `^^` (`Xor`) | left |
| 8 (`UNOP_PREC`) | unary `!` `-` | prefix |
| 9 (`APP_PREC`) | application (`f a b`), `Some e`, `oget e`, `rem m k` | — |
| 10 (`ATOM_PREC`) | variables, literals, tuples, projections, `m.[k]`, `m.[k <- v]`, `empty`, `None<:t>`, nullary `App` | — |

**One deviation from the story's §3.2 table, found by compiling, not
guessed**: the story places `^^` between `/\` and `=`. `ecParser.mly`'s
`%left`/`%right` declarations put `^^` in the `HAT` token class, which is
*tighter* than `*`/`%/`/`%%` and the comparisons. Compiling
`a < b ^^ a <= b` unparenthesised confirmed it: EasyCrypt groups it as
`a < (b ^^ a) <= b` and rejects `b ^^ a` as a type error (`^^` applied to two
`int`s). `render.rs` places `Xor` above `Mul`/`Div`/`Mod` accordingly (see
the doc comment on `binop_info`). Every other row matches the story's table,
and all six required precedence tests
(`a /\ b \/ c`, `(a \/ b) /\ c`, `!(a /\ b)`, `a = b /\ c = d`,
`(a + b) * c`, `a => b => c`) pass unchanged either way — the deviation only
matters once `Xor` is mixed with comparisons/arithmetic, which those six
don't exercise.

A negative integer literal (`EcExpr::Int(n)` with `n < 0`) is pinned to
`APP_PREC` rather than `ATOM_PREC`: `f -1` lexes as `f - 1` (verified by
compiling), so it still needs parens exactly where an application argument
would (`f (-1)`), but not as a binop operand (`a + -1` is fine bare).

`EcUnop::Not`/`Neg` are both modelled at one precedence (`UNOP_PREC`,
tighter than every binop, looser than application) rather than
EasyCrypt's real, subtler placement of `!` (`ecParser.mly` puts `NOT`
between `AND` and `EQ`, i.e. looser than comparisons/arithmetic/`Xor`).
This is a deliberately conservative simplification, not a verified fact:
the kitchen sink never nests `Unop` inside a `Binop` other than
`Or`/`Not` (`b \/ !b`), where both tables agree `Not` binds tighter. If a
later story renders `Unop` nested inside `Eq`/comparisons/`Xor`/arithmetic,
**verify against real EasyCrypt before trusting `UNOP_PREC`** — it may
under- or (more likely, since it's conservative) over-parenthesise there.

## 4. Mangling rules and reserved prefixes (`names.rs`)

Implemented exactly as specified in §3.3: `-` → `_` first; `Module`/
`ModuleType` uppercase the first letter and prefix `M_` on a leading digit
or `_`; every other kind prefixes `d_` when the (post-`-`-replacement) name
starts uppercase, is a keyword, or already starts with `ec_`; leading `_` is
left alone; a same-raw-name remangle is idempotent; a different-raw-name
collision in the same `NameKind` namespace is a hard
`NameError::Collision { kind, a, b, mangled }`. The `KEYWORDS` list (160
words, sorted, `ecLexer.mll` cited) is checked sorted by a unit test since
`mangle_name` binary-searches it.

## 5. Other EasyCrypt facts found by compiling (worth knowing for later stories)

- **`int` has no `>`/`>=` in the standard library.** Only
  `theories/datatypes/Real.ec` defines `( > )`/`( >= )` (as `abbrev`s over
  `<`/`<=`, flipped). A bare `a > b` on `int`s resolves to `Real.>` and
  fails to typecheck. **A later story translating a Domino `>`/`>=` on
  integers must either flip it to `<`/`<=` at translation time, or emit a
  local `int` overload** (the kitchen sink does the latter, as a fixture,
  to exercise `EcBinop::Gt`/`Ge`: `op (>) (x : int) (y : int) : bool = y < x.`
  compiles and coexists with `Real`'s abbrev because EasyCrypt overloads by
  type as well as name). Whichever a later story picks, it isn't optional —
  omitting it means generated code with `>`/`>=` on `int` won't compile.
- **`^^` needs `require import Bool`** (`theories/core/Bool.ec`); it is not
  pulled in by `AllCore`.
- **`%/`/`%%` need `require import IntDiv`**; also not in `AllCore`.
- **`(int, bool) fmap` needs `require import FMap`**.
- Confirmed by compiling (used as-is in the kitchen sink, no surprises):
  tuple projection `` s.`1 ``; record field projection `` r.`fld ``; record
  type decl `type t = { f : ty; ... }.` (braces, not `{| |}` — that's only
  for record *literals*); anonymous `section.` / `end section.`; `declare
  module A <: T { -Restriction }.` with a real restriction target; a
  functor module type `module type Adv (O : Proto) = { ... }`; a functor
  module `module F (P : T) = { ... }` and its application `module M =
  F(A).`; `clone Base as Inst with type t <- ty, op o <- e, ...` with
  comma-separated multiple overrides; `var x : t <- e;` (combined
  type-and-init local declaration, per the story's "always render the type
  too" rule); a numeric memory binder `lemma foo &1 : M.x{1} = M.x{1}.`
  (`&1` is a legal memory identifier, so `EcExpr::Qualified { mem: Some(1),
  .. }` needs no special-casing beyond a plain `LemmaBinder::Memory("1")`).

## 6. Golden file / compile check

- Golden file: `testdata/easycrypt/story01/kitchen-sink.ec`, checked
  byte-for-byte against `render_file(&kitchen_sink())` in
  `kitchen_sink_matches_golden_file`.
- Compile check: `kitchen_sink_compiles_under_easycrypt` shells out to
  `easycrypt compile -I testdata/easycrypt/story01
  testdata/easycrypt/story01/kitchen-sink.ec`. It skips (prints to stderr
  and returns, does not fail) when `easycrypt config` can't be run. In this
  environment `easycrypt` **was** on `PATH` and the check ran for real.

Per §6 of the overview ("if you discover a fact a later story will need, add it to that story's
'Inherited from earlier stories' section"), the `int` `>`/`>=` fact above (§5, second bullet) has
been added to `docs/stories/easycrypt/02-types-and-expressions.md` §2.1, since story 02's
`GreaterThen`/`GreaterThenEq` → `>`/`>=` mapping (its §3.2) would otherwise emit code that doesn't
compile.

## 7. Notes for follow-up (not this story's scope)

- No `theory ... end` `EcItem` exists yet. Story 03+ package theories will
  need one (or the exporter always writes one theory per file and never
  needs the item — worth deciding explicitly when that story starts, since
  `Clone`'s `base` currently has to name an already-`require`d theory/file).
- `render_stmt`, `render_expr`, `render_type` are `pub fn` as required for
  story 08's listing; `render_file` is the only other public entry point.
  Everything else in `render.rs` is private.
