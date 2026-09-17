# Story 14 — Package import interfaces, composition-local adapters, and the `Pkg_` prefixes

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** stories 03 (package variants), 04 (games/router/`Interfaces.ec`), 10 (flat layout),
11 (module-type dedup — this story deletes what 11 built; see §3.5).
**Blocks:** story 08 (EC IR lowering) and story 09 (debug on EasyCrypt) should be written against
the shape this story produces, not the pre-story-14 one.

---

## 1. Why this story exists

Two separate complaints from the owner, fixed together because each one alone would rewrite every
golden file.

### 1.1 A package is duplicated because of how it is composed

`VariantKey` (`src/writers/easycrypt/package.rs:50`) keys a package's EasyCrypt module on
*pkg name + int params + fn params + the recursively-embedded keys of everything it imports from*.
That last component means the **wiring** splits a package into variants. `hello-world` shows it at
its most absurd — `testdata/easycrypt/story03/hello-world/Variant_Fwd_v1.ec` and
`Variant_Fwd_v2.ec` are byte-identical except for one line:

```
module Fwd_v1 (P_Rand : Interfaces.Rand_i)   = { …23 identical lines… }.
module Fwd_v2 (P_Fwd  : Interfaces.Fwd_v1_i) = { …23 identical lines… }.
```

Both the parameter *name* (`P_<callee instance>`) and its *type* (the callee's exported interface)
are facts about a composition, not about the package `Fwd`. The arity is too: `build_functor_params`
(`package.rs:395`) emits one parameter per distinct callee instance.

**The rule the owner wants:** a package's EasyCrypt module is a function of the package and its
`Bits(...)` instantiation, *nothing else*. A package declares, in its own file, one module type for
the oracles it expects; a composition is responsible for producing something of that shape —
directly when one instance already is that shape, or through a small composition-local adapter
module when the expected oracles come from several instances.

### 1.2 The `Variant_` prefix

Three name layers exist today; all three get renamed:

| Layer | Today | After |
|---|---|---|
| package file / theory | `Variant_KX.ec` | `Pkg_KX.ec` |
| per-instance theory clone | `Pkg_<inst>` | `Cloned_Pkg_<inst>` |
| the instance as a module | `Inst_<inst>` (only when it has imports) | `Pkg_Inst_<inst>` (**always**, §3.4) |

### 1.3 How to land it

One story, three commits, so the goldens are regenerated once:

1. Import interface + adapters + the shrunken variant key (§3.1–§3.5) — the semantic change.
2. The prefix rename (§3.6) — mechanical.
3. Goldens and docs: regenerate `testdata/easycrypt/**`, update the module-level doc comments.

`CONTEXT.md` and `00-overview.md` were **already updated** when this design was settled: the
glossary defines *package variant*, *import interface* and *import adapter* as this story
implements them, and the overview's decision table carries the "Amended by story 14" rows. Make the
code agree with them; if you find you must deviate, change the glossary in the same commit and say
so in the report. Do **not** edit `docs/easycrypt-export.md` — it is the owner's original
requirement document, and `00-overview.md` is what wins where they disagree.

The *why* behind §3.2–§3.4, and the alternatives that were rejected, are recorded in
`docs/adr/0001-packages-declare-their-own-import-interfaces.md`. Read it before proposing to type a
package's functor parameter by its callee's interface again.

## 2. Facts this story rests on — already verified, do not re-derive

### 2.1 EasyCrypt (same binary stories 10–13 used, `~/.opam/easycrypt/bin/easycrypt`, `r2026.06`-era)

Every shape below was compiled during the design of this story. Re-verify them once at the start
of implementation; do not treat any of them as an open question.

| Shape | Result |
|---|---|
| `module type Imports` and `module Imports (O : Imports)` in one theory | **accepted** — module and module-type namespaces are disjoint (and `NameKind::ModuleType`, `names.rs:182`, is already a separate registry) |
| adapter ascribed to the **uncloned** `A.Imports`, passed to `Cloned_Pkg_m.M` which expects `Cloned_Pkg_m.Imports` | accepted — matching is structural across the clone boundary (story 11 §1.1 found the same) |
| a callee passed directly while having **extra** procs the type does not mention | accepted (width subtyping) |
| `clone B as Pkg_Inst_n.` — a non-functor clone named directly after the instance | accepted, but **not** the shape §3.4 chose; it is listed because it proves a clone alias may be named anything but its source |
| `module Pkg_Inst_n = Cloned_Pkg_n.N.` then `Pkg_Inst_n.s{m} = Cloned_Pkg_n.N.s{m}` | closed by `done` — **an alias denotes the same memory cell** |
| `module Pkg_Inst_m = Cloned_Pkg_m.M(Pkg_Inst_n).` then `Pkg_Inst_m.ctr{m} = Cloned_Pkg_m.M.ctr{m}` | closed by `done` — **a functor application's state is addressable through the application name** |
| `declare module Adv1 <: Adv { -Pkg_Inst_m, -Pkg_Inst_n }.` | accepted — restrictions work through those names |
| a functor **application** passed directly as another functor's argument, two levels deep | accepted |
| an adapter module calling into a functor application (`r <@ Pkg_Inst_fwd.f();`) | accepted |

The last three are what make §3.4's uniform `Pkg_Inst_<inst>` viable, and the fifth/sixth are what
let `proof.rs` drop the variant name from every dotted path.

### 2.2 Domino guarantees (parser, already enforced)

- **Every declared import is wired.** `src/parser/composition.rs:270-290`
  (`MissingEdgeForImportedOracleError`) rejects a composition in which some
  `inst.pkg.imports` entry has no edge. So an import interface built from `pkg.imports` is always
  exactly satisfiable by the composition, and there is no "unwired import" case to design for.
- **Import name and callee oracle types agree.** `composition.rs:510` rejects an edge whose
  `src_oracle_sig` and `dst_oracle_sig` don't `types_match` *after* instantiation. So the adapter's
  forwarding procs never need a cast, and the direct-pass case of §3.4 is always type-correct.
- **Import names are unique per instance.** `composition.rs:525`
  (`DuplicateEdgeDefinitionError`) rejects two edges out of one instance with the same
  `edge.name()`. So an import interface's proc list has no duplicates by construction.
- **`edge.name()` is the caller's name; `edge.sig().name` is the callee's.** `src/package.rs:121`:
  `alias().unwrap_or(&self.sig().name)`, and the parser stores the *destination's* authoritative
  sig in the edge (`composition.rs:539`). The alias syntax is
  `compose_assign_alias = identifier ~ ":" ~ identifier ~ "of" ~ identifier`
  (`src/parser/ssp.pest:375`), i.e. `<caller's import name>: <callee oracle> of <callee instance>`.
  `example-projects/hello-world-oracle-rename-new` is the test bed.

## 3. Work to do

### 3.1 Shrink the variant key

`VariantKey` (`package.rs:50`) keeps `pkg_name` and `fn_params`; **drop `imports` entirely**, and
keep only those integer params that are actually baked into a type — i.e. filter `int_params` by
the existing `integer_param_used_as_width(pkg, name)` (`package.rs:247`). A non-width integer
param already becomes a module variable assigned by `init` (`param_needs_var`, `package.rs:375`),
so two instances differing only there render identically and must share one module.

Function params stay in the key: a `Fn` param is translated into a call to a named operator baked
into the body, so two instances with different functions genuinely render differently. (Making
them `init` arguments of arrow type is possible in EasyCrypt but is a separate, much larger story
— record it in §7, do not attempt it here.)

Consequences to expect and assert: `compute_key` no longer needs `computed`/`ordered_pkgs_idx`
sequencing at all (it stops being recursive), and `hello-world`'s `Fwd_v1`/`Fwd_v2` collapse into a
single variant named `Fwd`.

Extend `variant_comment` (`package.rs:434`) to spell out every keyed parameter, so a reader of
`Pkg_Fwd_v2.ec` can see what distinguishes it from `Pkg_Fwd_v1.ec` without diffing.

### 3.2 Each package declares its own import interface, in its own file

In `render_variant` (`package.rs:454`), build one module type from `inst.pkg.imports`, in
declaration order, and put it in the variant's own `EcFile` **before** the module:

```
(* Fwd: n = n *)
require import AllCore Distr FMap Int IntDiv Types.

module type Fwd_Imports = {
  proc d_UsefulOracle() : (int * bits_n) option
}.

module Fwd (O : Fwd_Imports) = { … }.
```

- **Name:** `<Variant>_Imports`. It is strictly longer than the module's own name, so it can never
  collide with it whatever the Domino package is called — the owner's stated worry, closed
  structurally rather than by the (true but unhelpful) fact that EasyCrypt tolerates the clash.
  Mangle it through `NameKind::ModuleType`.
- **Procs:** one per `pkg.imports` entry, named after the **import name** (`import.name`, which is
  the alias when the composition renames), mangled exactly the way `interfaces.rs:81`'s
  `build_variant_procs` mangles an oracle: `NameKind::Proc` for the name, `NameKind::Var` for each
  argument, return type `EcType::Option(...)`. Factor that shared shape out rather than copying it
  a third time — `build_variant_procs` itself is deleted by §3.5, so move the reusable part into
  `package.rs`.
- **Functor parameter:** a single `O`. `PackageScope::functor_params` (a per-callee map) collapses
  to a single optional name.
- **A package with no imports** gets no module type and no functor parameter, exactly as today.
- **`require Interfaces` disappears from package files** (`package.rs:561`): nothing in a package
  file references `Interfaces` any more. Package files require `Types` only.

### 3.3 Bodies must call the *import* name

`translate_invoke` (`package.rs:975`) currently calls
`Names::new().mangle(NameKind::Proc, &edge.sig().name)` on the module
`functor_params[&edge.to()]`. Both halves change: the module is always `O`, and the proc is
`edge.name()` — the caller's import name. This is the one change in this story that alters
generated *oracle bodies* rather than just names and wiring, and it is what makes a package's
module independent of its composition. `example-projects/hello-world-oracle-rename-new` is the
project that distinguishes the two spellings; it must be in the test set.

### 3.4 Composition files: clones, instances, and adapters

In `render_game_file` (`game.rs:175-260`), for each instance in `ordered_pkgs_idx()` order:

1. `clone Pkg_<Variant> as Cloned_Pkg_<inst>.` — **always**, for every instance.
2. Its imports, if any, are satisfied in one of two ways:
   - **Direct pass** — iff *every* edge out of this instance goes to the **same** callee instance
     **and** no edge out of it is aliased (`edge.alias().is_none()`, i.e. each import name is
     already the callee's oracle name). Then the argument is `Pkg_Inst_<callee>`. A callee with
     more oracles than the interface demands is fine (width subtyping, §2.1).
   - **Adapter** — otherwise. Emit, immediately before the instance module:
     ```
     module Pkg_Imports_<inst> : Pkg_<Variant>.<Variant>_Imports = {
       proc d_<import name>(…) : … option = {
         var r : … option;
         r <@ Pkg_Inst_<callee>.d_<callee oracle>(…);
         return r;
       }
       …
     }.
     ```
     One proc per `pkg.imports` entry, in the same order as the interface, each forwarding to the
     instance the matching edge points at. Ascribe it to the **uncloned** `Pkg_<Variant>`'s type
     (§2.1 row 2) — it is the early error that catches a mismatch at `easycrypt compile` time
     instead of at the application site.
3. `module Pkg_Inst_<inst> = Cloned_Pkg_<inst>.<Variant>(<arg>).` when it has imports, and
   `module Pkg_Inst_<inst> = Cloned_Pkg_<inst>.<Variant>.` — a plain alias — when it does not.

Step 3's "always give the instance a module name" is the decision that pays for itself elsewhere:
every call site (`module_ref[idx]` in the router), every state path in `proof.rs`, and every
adversary restriction becomes `Pkg_Inst_<inst>…` with **no variant-name component**, all verified
to denote the same cells (§2.1 rows 5–7).

Emission order within the file: all clones (in `ordered_pkgs_idx()` order), then per instance in
that same order its adapter (if any) followed by its `Pkg_Inst_` module, then the router, then the
experiment. A callee's `Pkg_Inst_` is always defined before any adapter or application that names
it, because `ordered_pkgs_idx()` visits callees first.

Both `Pkg_Imports_<inst>` and `Pkg_Inst_<inst>` derive from the existing per-composition
`inst_names` registry (`game.rs:186`), so a residual mangling collision stays a hard error.

### 3.5 Delete the per-variant module types from `Interfaces.ec`

With §3.2, `Interfaces.<Variant>_i` has no consumers — `package.rs:422` was the only one. Delete
the whole package-variant section of `build_interfaces_file` (`interfaces.rs:135-212`), including
`build_variant_procs` (`interfaces.rs:81`) and story 11's grouping/`{ include … }` aliasing.
`Interfaces.ec` becomes exactly the game interfaces and their adversary types.

Say plainly in the implementation report that this **supersedes story 11**, which was a
readability change to a section that no longer exists — not that story 11 was wrong. Keep
`EcItem::ModuleType::includes` and `render.rs`'s support for it (it is tested and costs nothing);
just stop producing it. The `variant_groups` loop and its two unit tests
(`hello_world_fwd_v1_and_fwd_v2_alias_rand`, `simple_4whs_no_variant_module_type_is_an_alias`) go
away with the section they test.

`discover_compositions`, `build_export_procs`, `comp_mangled`/`iface_name`/`adv_name` are all
untouched.

### 3.6 The prefix rename

- `export.rs:193`: `Variant_{}.ec` → `Pkg_{}.ec`. `Comp_`, `Eq_`, `Types.ec`, `Interfaces.ec` are
  unchanged; story 10's collision-free-theory-names property is preserved, since `Pkg_` and `Comp_`
  remain disjoint prefixes over two independent `Names` registries.
- `game.rs:192`/`:222`/`:245`/`:258`: `Pkg_<inst>` → `Cloned_Pkg_<inst>`, `Inst_<inst>` →
  `Pkg_Inst_<inst>` (now unconditional, §3.4), `clone`'s `base` and the `require` list
  `Variant_<V>` → `Pkg_<V>`.
- `proof.rs:172` (`restrictions_for`) and `proof.rs:205` (`build_side_record_lit`):
  `<Comp theory>.Pkg_<inst>.<Variant>` → `<Comp theory>.Pkg_Inst_<inst>`. `CompLayout.variant_names`
  becomes unused — delete the field and the `variant_name_map` plumbing that feeds it if nothing
  else needs it.
- `invariant.rs` needs **no** change: it builds record *types* and field names, never module paths
  (checked).
- Update the module-level doc comments that describe the old layout: `game.rs:10-19`,
  `package.rs:193-196`, `interfaces.rs:3-11`, `export.rs:6`, `ast.rs:148`, `ast.rs:277`.

### 3.7 Worked examples to check the design against

**`hello-world` / `BigComposition`** — `fwd` imports from `rand`, `fwd2` imports from `fwd`, both
unaliased and single-callee, so no adapter is generated anywhere and `Fwd` has one variant:

```
require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Pkg_Rand Pkg_Fwd.

clone Pkg_Rand as Cloned_Pkg_rand.
clone Pkg_Fwd  as Cloned_Pkg_fwd.
clone Pkg_Fwd  as Cloned_Pkg_fwd2.

module Pkg_Inst_rand = Cloned_Pkg_rand.Rand.
module Pkg_Inst_fwd  = Cloned_Pkg_fwd.Fwd(Pkg_Inst_rand).
module Pkg_Inst_fwd2 = Cloned_Pkg_fwd2.Fwd(Pkg_Inst_fwd).

module Game_BigComposition : Interfaces.Iface_BigComposition = { … Pkg_Inst_fwd2.d_UsefulOracle … }.
```

Two files (`Variant_Fwd_v1.ec`, `Variant_Fwd_v2.ec`) become one (`Pkg_Fwd.ec`); a functor
application is passed directly as a functor argument, which §2.1 verified.

**`kem-dem-cca-ssp` / `Game_CCA_DEM`** — `DEM: { DEM_ENC: Scheme_DEM, DEM_DEC: Scheme_DEM, GET: Key }`
spans two callees, so `DEM` gets the adapter; it is the motivating multi-callee case.

**`hello-world-oracle-rename-new` / `MediumComposition`** —
`fwd: { ChangeNameUsefulOracle: UsefulOracle of fwd, AnotherUsefulOracle: UsefulOracle of rand }`
exercises both an alias and two callees, *and* two import names bound to the same callee oracle. Its
adapter has two procs, one forwarding to `Pkg_Inst_fwd.d_UsefulOracle` and one to
`Pkg_Inst_rand.d_UsefulOracle`, while `Pkg_Fwd.ec` mentions only `d_ChangeNameUsefulOracle` /
`d_AnotherUsefulOracle`. This project is the proof that §3.3 landed.

## 4. Acceptance criteria

- [ ] `hello-world` exports **one** `Pkg_Fwd.ec` (no `_v1`/`_v2`), and its module reads
      `module Fwd (O : Fwd_Imports)`.
- [ ] No generated package file mentions `Interfaces`, and no `Interfaces.ec` contains a
      `<Variant>_i` module type — only `Iface_*` and `Adv_*`.
- [ ] Every instance in every `Comp_*.ec` is reachable as `Pkg_Inst_<inst>`; the string `Inst_`
      never appears without the `Pkg_` prefix, and `Variant_` appears nowhere in any generated file
      or file name.
- [ ] An adapter is emitted **exactly** when the §3.4 rule says so: none in `hello-world`, one for
      `DEM` in kem-dem's `Game_CCA_DEM`, one for `fwd` in `hello-world-oracle-rename-new`'s
      `MediumComposition`.
- [ ] `hello-world-oracle-rename-new` exports: the package file's interface and body use the
      *import* names, the adapter maps them to the callee oracle names.
- [ ] `Eq_*.ec` restrictions and game-state record literals name `Comp_<X>.Pkg_Inst_<inst>.<field>`,
      with no variant component.
- [ ] Every generated file still compiles with `easycrypt compile -I .` for Simple4WHS, Full4WHS and
      kem-dem-cca-ssp (the three `*_full_tree_compiles_in_dependency_order` tests), with no new
      failure beyond the two pre-existing gaps recorded in story 07 §6.1/§6.2.
- [ ] `CONTEXT.md`'s EasyCrypt section matches what is generated (the glossary was updated when the
      design was settled; the code must be made to agree with it, not the other way round).
- [ ] Deterministic output; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace && cargo test --workspace
D=$PWD/target/debug/domino
for p in example-projects/hello-world example-projects/hello-world-oracle-rename-new \
         example-projects/kem-dem/kem-dem-cca-ssp; do (cd $p && $D easycrypt --theorem <T>); done
ls _build/easycrypt/*/            # no Variant_*.ec
grep -rn "module type" _build/easycrypt/*/Interfaces.ec   # only Iface_*/Adv_*
grep -rn "Pkg_Imports_" _build/easycrypt/*/Comp_*.ec      # only where §3.4 says
(cd _build/easycrypt/<T> && easycrypt compile -I . Types.ec Interfaces.ec Pkg_*.ec Comp_*.ec Eq_*.ec)
```

`hello-world` and `simple-KEM-example` still fail *export* on the pre-existing invariant-dialect gap
(story 07 §6.2, `unsupported SMT sort <GameState_…>`) before any file is written, so for those two
verify the package/interface criteria through targeted unit tests on the rendered `EcFile`s, exactly
as story 11 §3 did.

**Goldens:** `testdata/easycrypt/story03/*/Variant_*.ec` are renamed to `Pkg_*.ec` and rewritten;
`testdata/easycrypt/story04/*/Comp_*.ec` and `Interfaces.ec` are rewritten; the checked-in `.eco`
files beside them are compiler artifacts and must be regenerated or dropped in the same commit.
Regenerate from the translator, then read the diff — do not accept it blind, this story changes
oracle bodies (§3.3).

## 6. Notes / risks

- **§3.3 is the only place semantics can silently break.** Switching from `edge.sig().name` to
  `edge.name()` is invisible in every project that has no aliases — every golden except
  `hello-world-oracle-rename-new` would pass either way. Test that project explicitly.
- **One more inline hop in proofs.** Where an adapter is generated, a proof that inlines a package
  oracle now passes through `Pkg_Imports_<inst>.d_…` first. That is the price of the design and the
  reason for the "only if needed" rule in §3.4; stories 08/09 must handle both depths.
- **Do not ascribe package modules to an "exports" module type.** It is tempting now that
  `<Variant>_i` is being deleted, but `init` is deliberately absent from those signatures and the
  router calls `init`. Out of scope.
- **Do not reintroduce per-callee functor parameters** as an optimisation for the multi-callee case.
  The single parameter is what makes the package file composition-independent, which is the whole
  point of the story.
- **Cyclic compositions.** Everything here assumes `ordered_pkgs_idx()` yields a callees-first
  order, as story 04 already does. If a composition is cyclic, this story does not make it worse,
  but the failure mode (an EasyCrypt forward reference) is now an adapter's forward reference. A
  pointed export error would be a fine follow-up; do not build it here.

## 7. State handed to the next story

Record in `14-…-IMPLEMENTATION-REPORT.md`:

- Which projects lost variants, with before/after counts (expect `hello-world`: 3 → 2).
- Which instances got adapters and which got a direct pass, per example project — this is the table
  stories 08/09 need to know how deep to inline.
- Whether `CompLayout.variant_names` and the `variant_name_map` plumbing in `proof.rs` could be
  deleted outright, or something still needs a variant's name at proof-writing time.
- The re-verification of §2.1's EasyCrypt table against the binary actually installed at
  implementation time.
- The "function params as `init` arguments of arrow type" idea (§3.1) — the last remaining reason a
  package can have several variants for reasons other than `Bits(...)`.
