# Story 11 — Shared package module types in `Interfaces.ec`

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 04 (`Interfaces.ec`). Do **after** story 10, which moves the goldens.
**Blocks:** nothing.

---

## 1. Why this story exists

`Interfaces.ec` emits one `module type <Variant>_i` per package variant
(`src/writers/easycrypt/interfaces.rs:148`), listing every oracle that variant's package defines.
When several variants have the same oracle signatures, the file repeats itself verbatim. In
`hello-world` today, three module types are byte-identical:

```
module type Rand_i   = { proc d_UsefulOracle() : (int * bits_n) option
                         proc d_UselessOracle(x : int) : int option }.
module type Fwd_v1_i = { …the same two lines… }.
module type Fwd_v2_i = { …the same two lines… }.
```

Game interfaces already avoid this: `interfaces.rs:184-200` groups compositions by their structural
`Vec<ProcSig>` and emits one `Iface_<X>` per group with an `(* … also cover: … *)` comment. This
story applies the same treatment one level down, to package-variant module types.

### 1.1 What this story is *not*

The original motivation was "if some other package imports them, there is no need to have different
versions" — i.e. a fear that duplicated module types force an importing package to be emitted twice.
**That fear does not hold.** Verified against r2026.06-12-g7e192dd:

- **Module-type matching is structural, not nominal.** `module M (P : Fwd_v1_i)` applied to
  `R : Rand_i`, where `Fwd_v1_i` and `Rand_i` are *independently declared* and structurally
  identical, compiles.
- **Matching is width-subtyping.** A module with *more* procedures than the type demands also
  matches: `M(O)` where `O : Other_i` has an extra `extra()` procedure compiles.

So `functor_params` (`src/writers/easycrypt/package.rs:398-422`) pointing a caller's functor
parameter at one specific `<Variant>_i` is already sound even when the call site supplies a
different-but-compatible variant. **This story is a readability and file-size change, not a
correctness fix.** Write it that way — do not claim in the implementation report that it fixed a
bug.

It is worth doing anyway: 4WHS's `Prot_i` alone is five `proc` lines of eleven-component tuple
types, and repeating a near-copy of it for `Prot_NoKey` and `Prot_NoPrf` is a large amount of noise
in the one file a human reads to understand the export's shape.

## 2. Inherited from earlier stories

- `build_variant_procs(pkg) -> Vec<ProcSig>` (`interfaces.rs:81`) — every oracle the variant's
  package defines, mangled, `init` deliberately excluded.
- `package::discover_variants(theorem)` and `package::assign_names(&discovered, &mut names)` give
  the variant list in discovery order and their EasyCrypt names.
- `ProcSig` derives structural equality; the game-interface grouping at `interfaces.rs:191-200`
  already relies on it. Reuse that exact grouping shape.
- `package.rs:419` is the only consumer of the `<Variant>_i` name:
  `params.push((param_name, format!("Interfaces.{callee_variant}_i")))`.

## 3. Work to do

### 3.1 Group variants by signature

Mirror `interfaces.rs:191-200`: build `Vec<Vec<ProcSig>>` in variant-discovery order, group indices
by structural equality, preserve first-discovery order across groups and within a group.

### 3.2 Emit one real type per group, plus one alias per other member

The owner's decision (Q2) is that **every variant keeps a module type spelled after itself**, so no
call site has to reference an unrelated package's name. The alias syntax is:

```
module type Rand_i   = { proc d_UsefulOracle() : (int * bits_n) option
                         proc d_UselessOracle(x : int) : int option }.

(* Fwd_v1_i, Fwd_v2_i share Rand_i's signature *)
module type Fwd_v1_i = { include Rand_i }.
module type Fwd_v2_i = { include Rand_i }.
```

**`module type X = Y.` is a parse error** — verified, `parse error` at the `=`. The `{ include Y }`
form is the working one, and `M(R)` where `M (P : Fwd_v1_i)` and `R : Rand_i` compiles through it.

`package.rs:419` needs no change at all: it still asks for `Interfaces.<callee_variant>_i` and that
name still exists.

### 3.3 AST support

`EcItem::ModuleType { name, params, procs }` (`ast.rs`) cannot express `{ include X }`. Add the
minimal thing that can — either an `includes: Vec<String>` field alongside `procs`, or a separate
`EcItem::ModuleTypeAlias { name, includes: Vec<String> }`. Prefer whichever keeps `render.rs`
simpler; a module type that both includes and declares procs is not needed by this story.

## 4. Acceptance criteria

- [ ] `hello-world`'s `Interfaces.ec` declares the two-oracle signature **once** and gives
      `Fwd_v1_i` and `Fwd_v2_i` as `{ include Rand_i }`.
- [ ] 4WHS's `Interfaces.ec` is unchanged in content: no two of its seven variants share a
      signature (`Prot`/`Prot_NoKey`/`Prot_NoPrf` differ in their state-tuple shape,
      `KX`/`KX_NoKeys`/`KX_NoPrf` in oracle count), so this is a deliberate no-op there. Assert it.
- [ ] Every generated file still compiles with `easycrypt compile -I .`, including the game files
      that apply these functors.
- [ ] Grouping is by structural `Vec<ProcSig>` only — a comment lists the group's members.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace && cargo test --workspace -p domino easycrypt
D=$PWD/target/debug/domino
cd example-projects/hello-world && $D easycrypt --theorem Proof
cd _build/easycrypt/Proof && grep -n "module type" Interfaces.ec
easycrypt compile -I . Interfaces.ec
```

## 6. Notes / risks

- **Alias direction is load-bearing.** `Fwd_v1_i = { include Rand_i }` requires `Rand_i` to be
  declared *earlier in the file*. Discovery order gives that for free as long as the canonical
  member is the group's first element — keep it that way.
- **Do not dedup across the package/game boundary.** A package variant's signature list and a
  composition's export list can coincide by accident; they are different concepts with different
  lifetimes and must stay separate module types.
- **Do not try to exploit width-subtyping.** It is tempting to emit one maximal module type and let
  every variant match it. Don't: the functor parameter type is what tells a reader (and story 08's
  lowering) which oracles a caller may actually invoke.

## 7. State handed to the next story

Record in `11-…-IMPLEMENTATION-REPORT.md`: the AST shape chosen for the alias, which projects
actually produced groups larger than one, and the confirmation that 4WHS was unchanged.
