# Story 04 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (282 passed, 4 pre-existing
`#[ignore]`d, none new) and `cargo clippy --workspace --all-targets` are all clean. `easycrypt`
(`r2026.06-12-g7e192dd`) was on `PATH`, so every `*_compiles`/`*_match_golden` test ran for real,
and the full `Types.ec` + `Interfaces.ec` + `packages/*.ec` + `games/*.ec` set for both projects
was additionally compiled by hand with the exact recipe from §5 of this story (`-I . -I packages
-I games`, every file, in dependency order) — all exit 0.

## 1. What exists

Two new files, both registered as `pub mod` in `src/writers/easycrypt/mod.rs`:

- `src/writers/easycrypt/interfaces.rs` (~360 lines): `Interfaces.ec`.
- `src/writers/easycrypt/game.rs` (~570 lines): `games/<Comp>.ec`.

Plus three small, necessary changes to earlier stories' code (§6) and one genuinely new fact about
EasyCrypt (§5) that next stories — and anyone re-running story 02/03's own tests — need.

```rust
// interfaces.rs
pub struct InterfacesOutput {
    pub file: EcFile,
    pub comp_mangled: HashMap<String, String>, // comp.name -> mangled base ("Hybrid0", "PRF_Game", ...)
    pub iface_name: HashMap<String, String>,   // comp.name -> "Iface_<X>" (may be shared)
    pub adv_name: HashMap<String, String>,     // comp.name -> "Adv_<X>"  (may be shared)
}
pub fn build_interfaces_file(theorem: &Theorem<'_>) -> Result<InterfacesOutput, EcExportError>;

// game.rs
pub struct GameFile { pub name: String, pub file: EcFile } // name = comp_mangled entry
pub fn compute_game_files(theorem: &Theorem<'_>) -> Result<Vec<GameFile>, EcExportError>;
```

`compute_game_files` calls `build_interfaces_file` internally (it needs the `Iface_<X>`/`Adv_<X>`
grouping decision and the shared `comp_mangled` map), so story 05 only needs to call
`build_interfaces_file` once for `Interfaces.ec` and `compute_game_files` once for `games/*.ec`;
each `GameFile.name` is exactly the basename to write `games/<name>.ec` under.

Tests are inline (`#[cfg(test)] mod tests`), following story 02/03's precedent.

## 2. Distinct compositions, not game instances

`interfaces::discover_compositions(theorem)` (`pub(super)`, shared with `game.rs`) dedups
`theorem.instances` by `comp.name`, first-discovery order. Verified against `Simple4WHS`: its ten
`instance`s collapse to exactly four compositions — `Hybrid0` (from `Real`/`Ideal`/`Hybrid0`),
`Hybrid1`, `Hybrid2` (from `Hybrid2`/`Hybrid3`/`Real_Hybrid3`/`Ideal_Hybrid3`), `PRF` (from
`Real_PRF`/`Ideal_PRF`) — matching the acceptance criterion's four names exactly and confirming
§2.2's "several game instances share one composition" empirically, not just by construction.

## 3. Package-variant naming is recomputed, not threaded through

Story 03's `compute_package_variants` returns rendered `Vec<PackageVariant>` — useful for
`packages/*.ec` but not for resolving *which* variant a given `(composition, pkg_idx)` uses. Rather
than changing story 03's public API/tests, three of its internals were widened from private to
`pub(super)`, unchanged otherwise: `VariantKey` (as an opaque `Hash + Eq` key — its fields stay
private), `compute_all_keys`, `discover_variants`, `assign_names`. `interfaces.rs` and `game.rs`
each call `discover_variants` + `assign_names` once, independently, to get the same
`HashMap<VariantKey, String>` `compute_package_variants` builds internally — computed twice (three
times counting a future story 05 orchestrator calling `compute_package_variants` too) instead of
threaded through, deliberately: these are pure functions of `theorem`, cheap for an export tool,
and this keeps story 03's already-reviewed code and golden tests completely untouched.
`compute_all_keys(comp)` is then called once per composition (`game.rs`) or once per discovered
variant's representative composition (`interfaces.rs`) to map `comp.pkgs[idx]` to its variant name.

Also widened: `integer_param_used_as_width` (unchanged), and two **new** `pub(super)` helpers
factored out of `render_variant`'s inline logic — no behavior change to story 03's output, confirmed
by its unchanged golden files (`KX.ec`, `Rand.ec`, etc. — only the `PRF`-related ones changed, and
only because of §5's unrelated naming fix):

```rust
pub(super) fn param_needs_var(pkg: &Package, name: &str, ty: &Type) -> bool; // Boolean, or Integer-and-not-width-only
pub(super) fn pkg_needs_init(pkg: &Package) -> bool;                        // state non-empty, or any param_needs_var
```

`game.rs` reuses both directly: `param_needs_var` to decide which of a callee's `pkg.params` the
router's `init` passes on (§4), and `pkg_needs_init` to skip a callee's `init` call entirely when
its variant has none (`Prot`/`Prot_NoKey`/`Prot_NoPrf`/`Prot_NoKey` in every 4WHS composition here
have neither state nor a value param, matching story 03's own finding for `Prot`).

## 4. The router's `init` signature, exactly

Composition-level `init` arguments are `comp.consts` filtered by **the same rule** `param_needs_var`
already applies to package params: `Boolean` always qualifies; `Integer` qualifies unless it is
*width-only* — but "width-only" has to be decided at composition scope now, since `comp.consts`
themselves aren't package params. `composition_int_const_is_width_only` (`game.rs`) walks every
package instance in the composition, and for each of *its own* declared params whose assigned
expression is a bare reference to this composition const (`GameIdentifier::Const` by name — see
§4.1 below for why this is exhaustive), asks `param_needs_var` about **that receiving package's own
param**. The composition const is width-only iff it is referenced at least once and *every*
reference feeds a width-only receiving param; an **unreferenced** const is conservatively *not*
width-only (kept as an `init` arg) — matching the story's own §6 note ("composition constants that
are unused still become init parameters ... keeping the signature positional and complete").

Verified end to end against the story's own worked example: `Hybrid0`'s consts are `n: Integer`
(width-only everywhere it's used — `Prot`'s and `KX`'s own `n` params are both width-only in their
packages, per story 03), `prf`/`mac: Fn` (never qualify, function consts become global operators),
`b: Bool` (qualifies) → `proc init(b : bool)`, byte-for-byte the story's example. `Hybrid2` adds
`bprf: Bool` (feeds `PRF`'s own `b` param, itself `Boolean` so always a var) → `proc init(b : bool,
bprf : bool)`.

### 4.1 Resolving a composition const inside a callee's param binding

A package instance's `params { name: expr }` binding, once instantiated into a `Composition`, is
always either a literal or a bare `Identifier::GameIdentifier(GameIdentifier::Const(c))` referencing
one of the *enclosing composition's own* declared consts — never a compound expression. This isn't
asserted, it's a consequence of `CountSpec::Identifier` requiring a bare `Identifier` (not an
arbitrary expression) for `type_extract` to resolve a `Bits` width through it, which must already
hold by the time export runs; `references_game_const`/`resolve_composition_const` (`game.rs`) rely
on this and `unreachable!` on anything else. The resolver maps `c.name` through the **same**
per-composition `Names` (`NameKind::Var`) the router's own `init` arg list was built with, so a
callee's init call (`Pkg_Prf.M_PRF.init(bprf)` in `Hybrid2`) always names the router's own arg, not
a re-derived one — verified by the golden files, not just argued.

## 5. A genuinely new EasyCrypt fact: reserved stdlib theory names

Exporting `Simple4WHS` end to end (not just golden-file-matching against hand-written fixtures)
surfaced a real `easycrypt compile` failure story 03's own compile checks never could, because they
never `require`d `PRF` from anywhere else: `4WHS`'s `PRF` package (story 03) and `PRF` composition
(this story) both mangle to the bare name `PRF`, and EasyCrypt's own standard library ships
`<install>/theories/crypto/PRF.eca` — **not** on `easycrypt config`'s reported default load path,
but still enough to make `require PRF.` fail with `cannot locate theory 'PRF'`, reproduced in total
isolation (a single `-I .` directory holding nothing but one local `PRF.ec`, nothing else on the
command line at all). Renaming the local theory (`PRFX` in the isolated repro) fixes it immediately,
confirming the cause.

Fix, in `names.rs`: a new `RESERVED_STDLIB_THEORY_NAMES: &[&str] = &["PRF"]` (deliberately small and
non-exhaustive — enumerating the whole stdlib is impractical and version-fragile, this grows only as
export hits another verified collision), checked in `Module`/`ModuleType` mangling alongside the
existing digit/underscore-prefix escape, both landing on the same `M_`-prefix scheme. This is a
**crate-wide** fix (`names.rs` is shared infrastructure, not story-04-local), so it also changed
story 03's own output: the `PRF` package variant is now named `M_PRF` everywhere. Story 03's golden
files, its `simple_4whs_variant_names`/`simple_4whs_prot_and_prf_compile_standalone` tests, and the
two *other* variant files that reference `Interfaces.PRF_i` as a functor-parameter type
(`KX_NoPrf.ec`, `Prot_NoPrf.ec` → now `Interfaces.M_PRF_i`) were all regenerated and re-verified to
still compile. `testdata/easycrypt/story03/4WHS/PRF.ec` is now `M_PRF.ec`.

### 5.1 A second, independent collision: package and composition namespaces aren't disjoint

Fixing 5's naming still left `packages/M_PRF.ec` (the package variant) and `games/M_PRF.ec` (this
story's *composition* file, before the fix below) sharing one theory name across two different
directories. Compiling `games/Hybrid2.ec` (which `require`s the `M_PRF` package variant) then failed
with `circular requires involving 'M_PRF'` — **even with no `-I games` on the command line at all**:
compiling a file under `games/` implicitly searches that file's own directory too, so
`games/M_PRF.ec` shadowed `packages/M_PRF.ec` regardless of explicit `-I` flags. This is a structural
gap, not a `PRF`-specific one: package-variant names (story 03's `Names`) and composition names
(this story's own, separate `Names`) are two registries with no shared namespace, so *any* package
and composition sharing a mangled base name would hit this, `PRF`/`PRF` collision (§5) or not.

Fix, in `interfaces.rs::build_interfaces_file`: after computing `comp_mangled` normally, check it
against the already-known set of package-variant names (`variant_name_map`'s values — computed
first, at the top of the same function); on a collision, re-mangle `"<comp.name>_Game"` instead. Only
`4WHS`'s `PRF` composition hits this today, landing on `PRF_Game` (`games/PRF_Game.ec`,
`Game_PRF_Game`, `Exp_PRF_Game`, `Iface_PRF_Game`\*, `Adv_PRF_Game`\*). The package-variant side
(story 03) was deliberately left untouched rather than escaped — it's already committed, tested, and
this story's own escape is enough. \*`PRF`'s own interface isn't shared with `Hybrid0`'s (different
export lists — see §7), so it does get freshly-named `Iface_PRF_Game`/`Adv_PRF_Game` here, not a
reused name; the `_Game` suffix only affects the *file/module* base, orthogonal to interface sharing.

## 6. Games files, as implemented

Matches §3.2 of the story exactly, verified against both worked examples (`Hybrid0` byte-for-byte,
modulo the `ec_r`→`ec_result` naming choice below) and both target projects' `easycrypt compile`:

- **Clones**: `clone <Variant> as Pkg_<InstMangled>.`, one per `comp.pkgs` entry, in
  `comp.ordered_pkgs_idx()` order (rightmost/no-imports first) — the story's own normative text, not
  the worked example's prose order (which visually lists `KX` before `Prot` despite `Prot` having no
  outgoing edges; the *rule* text says `ordered_pkgs_idx()`, so that's what's implemented and
  correctness doesn't actually depend on the choice — clones don't depend on each other, only the
  functor-alias step below does).
- **Instance-name mangling**: one dedicated, composition-scoped `Names` (`NameKind::Module`) shared
  across every instance's clone-alias *and* functor-alias name in that file — mirrors story 03's
  `functor_names` precedent, so two differently-named instances mangling to the same `Pkg_<X>` are a
  hard collision, not a silent one.
- **Functor aliases**: `module Inst_<InstMangled> = Pkg_<InstMangled>.<Variant>(<args>).`, only for
  an instance with outgoing edges; `<args>` are `module_ref[callee]` for each distinct callee in
  first-edge order (grouped exactly like story 03's `build_functor_params`, over the same
  `comp.edges`, so the order always lines up with that variant's own already-rendered functor
  parameter list — not re-derived from story 03, just the same simple loop written again since it's
  three lines and avoids exposing `build_functor_params` itself). Processed in `ordered_pkgs_idx()`
  order so a callee's `module_ref` entry (dotted clone path, or its own alias if it *also* has
  functor params) is always settled before a caller reads it — verified live in `Hybrid2`:
  `Inst_Prot = Pkg_Prot.Prot_NoPrf(Pkg_Prf.M_PRF)` then `Inst_KX = Pkg_KX.KX_NoPrf(Inst_Prot,
  Pkg_Prf.M_PRF)`, i.e. `KX_NoPrf`'s second functor argument is `Prf`'s *plain clone path* (no
  functor params of its own) while its first is `Prot`'s *alias* (which does).
- **`require`s**: two lines — the same base-library import line story 03's packages use
  (`AllCore Distr FMap Int IntDiv Types`), then a plain `require Interfaces <variants>.` listing every
  distinct variant this composition clones, in `ordered_pkgs_idx()` first-occurrence order.
- **Router** (`Game_<mangled> : Interfaces.Iface_<X>`): one `var abort_flag : bool`; `init` per §4;
  one export proc per `comp.exports` entry, **in that order** (verified load-bearing per the story's
  own note for story 07's proof-bullet ordering — nothing here reorders `comp.exports`). Each export
  proc's shape:
  ```
  proc d_<Name>(<args>) : T option = {
    var ec_result : T option <- None<:T>;
    if (!abort_flag) {
      ec_result <@ <module_ref[export.to()]>.<callee_proc>(<args>);
      if (ec_result = None<:T>) { abort_flag <- true; }
    }
    return ec_result;
  }
  ```
  This is semantically identical to the story's own worked example, with one intentional naming
  deviation: the temporary is called `ec_result` (called directly by the router's own call — no
  separate `ec_r`), matching story 03's package-oracle convention instead of introducing a second
  temp-naming scheme. `callee_proc` is mangled through a **fresh** `Names` (`NameKind::Proc`) —
  correct, not a gap: it reproduces the callee's already-validated `Proc` namespace, exactly
  `package.rs`'s `translate_invoke` reasoning.
- **Experiment** (`Exp_<mangled> (A : Interfaces.Adv_<X>)`): `proc run(<same args as init>) : bool`
  — `Game_<mangled>.init(<args>); b' <@ A(Game_<mangled>).run(); return b';`. Confirms §6's "the
  experiment is not parameterized by the game — the game is fixed per composition".

## 7. `Interfaces.ec`, as implemented

- **Package-variant module types** (`<Variant>_i`): one per story-03-discovered variant (via the
  `discover_variants`/`assign_names` recomputation, §3), listing every oracle the variant's *own*
  package defines (`pkg.oracles`, not filtered by who imports what), each arg/proc name mangled
  through a **fresh** `Names` per variant. No `init` — routers call `init` on the concrete clone.
- **Game interfaces** (`Iface_<X>`/`Adv_<X> (O : Iface_<X>) = { proc run() : bool }`): one per
  distinct **canonical export signature** — `comp.exports`, translated into a `Vec<ProcSig>` (proc
  name via `export.name()`, i.e. alias-or-`sig().name`; args and return type via `export.sig()`,
  wrapped `option`) through a **fresh per-composition** `Names`. Two compositions whose
  `Vec<ProcSig>` come out byte-for-byte structurally equal (proc names *and* arg names *and* types)
  share one interface, grouped in first-discovery order, primary composition (first in
  `theorem.instances` order) names it, later members get a `(* Iface_X/Adv_X also cover: Y, Z *)`
  comment immediately above. **Verified against `Simple4WHS`**: `Hybrid0` and `Hybrid1` share
  `Iface_Hybrid0`/`Adv_Hybrid0` (both 9-oracle, KX-shaped, and — non-obviously — so does `Hybrid2`,
  even though its `NewKey` routes to `Prf` instead of `KX`: `PRF`'s own `NewKey(ltk : Maybe(Bits(n)))
  -> Integer` happens to structurally match `KX`'s, so all *three* compositions end up on one shared
  interface, not just the two the acceptance bullet names). `PRF` (the composition) gets its own
  `Iface_PRF_Game`/`Adv_PRF_Game` (3 oracles: `NewKey`/`Eval`/`Hon` — a different shape entirely).
- **Dedup key includes argument names, not just types** — a real, accepted limitation: if two
  compositions' exports had matching oracle names/types but differently-spelled argument names, they
  would *not* be folded into one interface (each gets its own, correct but redundant). Not
  hypothetical-only-in-theory: checked directly against both target projects, where it happens to
  never bite (`KX`/`KX_NoKeys`/`PRF`'s overlapping oracles all use identical argument names, e.g.
  `ltk`, `ctr`, `msg`), so nothing here forced a type-only comparison; recorded as a real ProcSig
  design mirroring the story's own `Vec<ProcSig>` shape (`EcItem::ModuleType`'s `procs` field),
  exactly, so no separate "canonical key" type had to be invented.

## 8. Acceptance criteria, checked against what was actually built

- [x] `hello-world`'s `BigComposition` clones two instances of the `Fwd` package (`fwd`, `fwd2`) —
  confirmed by `big_composition_has_two_instance_clones_of_the_fwd_package`. **Not** "one variant
  cloned twice", though: per story 03's own already-flagged discrepancy (§2 of its report), `fwd` and
  `fwd2` are wired to differently-shaped callees (`rand` vs `fwd`) and so render as two *different*
  variants (`Fwd_v1`/`Fwd_v2`), each with its own clone — the acceptance bullet's literal "two clones
  of one variant" doesn't hold for this project, kept as designed (same call story 03 made) rather
  than forced by fabricating a different fixture. What the bullet's *export target* half claims
  ("router whose two exported oracles target different clones") also doesn't hold for the existing
  project: `BigComposition`'s `adversary: {...}` block routes **both** `UsefulOracle` and
  `UselessOracle` to `fwd2` alone (checked directly in `BigComposition.comp.ssp`) — no hello-world
  composition exports from two different instances. Both discrepancies are against the story's own
  illustrative bullet, not against §3's normative rules, which are followed exactly and are what the
  golden files/compile checks verify.
- [x] `4WHS` `Simple4WHS` exports `Hybrid0`, `Hybrid1`, `Hybrid2` and `PRF` — confirmed by
  `simple_4whs_games_match_golden`'s name-list assertion (§2). Golden files:
  `testdata/easycrypt/story04/{hello-world,4WHS}/{Interfaces.ec,games/*.ec}`.
- [x] `Interfaces.ec` reuses one game interface for `Hybrid0` and `Hybrid1` — confirmed (and, per
  §7, for `Hybrid2` too).
- [x] A composition whose instance has imported oracles produces a functor application with
  arguments in story 03's order — confirmed for both single-level (`Hybrid0`'s `KX`) and two-level
  (`Hybrid2`'s `KX_NoPrf(Inst_Prot, Pkg_Prf.M_PRF)`) cases.
- [x] `Types.ec` + `Interfaces.ec` + `packages/*.ec` + `games/*.ec` for 4WHS compile, `-I <out>` per
  file, dependency order — confirmed both by `cargo test` (each file's own `*_compiles` test) and by
  hand-running the story's exact §5 loop end to end; all exit 0.
- [x] Deterministic output (`rendering_is_deterministic` in both `interfaces.rs` and `game.rs`);
  `cargo build/test/clippy --workspace` clean.

## 9. State handed to the next story

- **Entry points**: `interfaces::build_interfaces_file(theorem) -> Result<InterfacesOutput,
  EcExportError>`; `game::compute_game_files(theorem) -> Result<Vec<GameFile>, EcExportError>`
  (calls the former internally). `GameFile { name, file }` — write `games/<name>.ec`.
- **File/module naming, exact strings for story 07's restrictions**: `games/<mangled>.ec`,
  `Game_<mangled>`, `Exp_<mangled>`, where `<mangled>` is `InterfacesOutput::comp_mangled[comp.name]`
  — the *composition's* own mangled base, **not necessarily** `comp.name` mangled bare: it gets a
  `_Game` suffix whenever it would otherwise collide with a package-variant name (§5.1) — today only
  `Simple4WHS`'s `PRF` composition (`comp_mangled["PRF"] == "PRF_Game"`). Package instance clones are
  `Pkg_<InstMangled>` (mangled via a *fresh, per-composition* `Names(Module)` over `PackageInstance
  ::name`, independent of `comp_mangled`); functor aliases (only for instances with outgoing edges)
  are `Inst_<InstMangled>`, same mangled instance name. **Restrictions must therefore name**
  `Pkg_<InstMangled>` (the clone), never `Inst_<InstMangled>` (the alias) — story 03's own note,
  reconfirmed: e.g. for `Hybrid0`, `{ -Game_Hybrid0.Pkg_KX.KX, -Game_Hybrid0.Pkg_Prot.Prot }`, not
  `-Game_Hybrid0.Inst_KX`.
- **`init` parameter order per composition**: `comp.consts`, filtered to `Boolean` or
  non-width-only-`Integer` (§4's `composition_const_needs_arg`/`composition_int_const_is_width_only`
  — same rule as story 03's `param_needs_var`, applied one level up), in `comp.consts`' own
  declaration order, mangled name **without** a trailing underscore (unlike a package's own `init`
  args — the router has no module var of the same name to disambiguate against). `Exp_<mangled>.run`
  takes the identical arg list, same names.
- **Export order per game interface == proof-bullet order**: `comp.exports`' own order, unmodified,
  both in the rendered `Iface_<X>` and in the router's own proc list — load-bearing per the story's
  §3.1 note, confirmed nothing here reorders it.
- **Interface reuse map**: `InterfacesOutput::iface_name`/`adv_name: HashMap<String, String>`,
  keyed by `comp.name` (not the mangled base) — every composition has an entry, including ones
  reusing another's interface.
- **New shared facts for later stories** (§5, §5.1): `names.rs::RESERVED_STDLIB_THEORY_NAMES` — a
  package/composition name colliding with an EasyCrypt stdlib theory is a real, hit-in-practice
  failure mode, not hypothetical; grow this list on the next verified collision, don't assume it's
  closed. Package-variant names and composition names are two independent namespaces that must not
  collide when their files can end up implicitly co-searched (`easycrypt compile` always implicitly
  searches a compiled file's own directory, regardless of explicit `-I` flags) — story 05's real
  project-layout writer should know this is already handled *for the composition side* by
  `comp_mangled`'s `_Game`-suffix escape, and should not need to re-solve it.
- **Golden-file paths**: `testdata/easycrypt/story04/{hello-world,4WHS}/{Interfaces.ec,games/*.ec}`,
  plus `Types.ec` and `packages/*.ec` copied in (kept in sync with story 03's own golden dir; not
  this story's own output) so the story's exact compile recipe (§5) can be run standalone from either
  directory.

## 10. Notes for follow-up (not this story's scope)

- §5.1's `_Game`-suffix escape only fires when a composition's mangled name collides with an
  *already-discovered* package variant name. It does not (and structurally cannot, given the
  ordering `interfaces.rs` computes things in) protect against the reverse — a package variant name
  colliding with a composition name computed *after* it — but no target project exercises that
  direction, and story 03's own naming is intentionally left untouched (§5.1).
- §7's dedup key equates two compositions' interfaces only when argument *names* match too, not just
  types. Fine for both target projects; a future project with the same exported shape but
  differently-spelled argument names would silently get two redundant (but each individually
  correct) interfaces instead of one shared one — not a correctness bug, just a missed optimisation,
  and not worth a speculative type-only comparison mode until a real project needs it.
- `PRF_Game` is an admittedly slightly awkward name (`games/PRF_Game.ec` containing `module
  Game_PRF_Game`) — a consequence of resolving §5.1 on the composition side to keep story 03
  untouched. If a future story finds this surfaces somewhere user-facing (it doesn't in this one),
  reconsidering which side eats the escape is a contained, localised change (one `if` in
  `interfaces.rs`).
