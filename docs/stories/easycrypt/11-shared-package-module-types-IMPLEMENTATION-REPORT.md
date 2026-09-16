# Story 11 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (342 passed, 4 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`~/.opam/easycrypt/bin/easycrypt`) was on `PATH`, so every compile-shaped test and the
story's own §5 recipe ran for real.

This is a **readability/file-size change only, not a correctness fix** — per §1.1, duplicated
module types were never a correctness problem (EasyCrypt module-type matching is structural and
width-subtyping), and nothing in this report claims otherwise.

## 1. What changed

### 1.1 AST shape chosen for the alias (§3.3)

Added a field to the existing `EcItem::ModuleType` variant rather than a separate `EcItem`
variant, since a module type in this epic is either a plain declaration or a pure alias, never
both, and reusing the existing variant kept `render.rs`, `package.rs` and every call site
untouched except the three constructors inside `interfaces.rs` (`ast.rs`):

```rust
ModuleType {
    name: String,
    params: Vec<(String, String)>,
    includes: Vec<String>,   // new
    procs: Vec<ProcSig>,
},
```

Convention: `includes` empty means a plain module type (every pre-existing construction site sets
it to `vec![]`, unchanged in output); `includes` with one entry and `procs` empty means a pure
alias, rendered as `module type X = { include Y }.` on one line — matching the exact shape in the
story text and the one EasyCrypt accepts (`module type X = Y.` is a parse error, verified again
during this story via `hello_world_interfaces_compiles`/the kem-dem full-tree compile). A module
type that both includes and declares its own procs is not produced anywhere and `render.rs`
handles it generically anyway (multi-line, `include` lines before `proc` lines) in case a later
story needs it.

`render.rs::render_module_type` gained the `includes: &[String]` parameter and the one-line
special case; every other renderer function is untouched.

### 1.2 Grouping (§3.1) and emission (§3.2)

`interfaces.rs::build_interfaces_file`'s package-variant loop now:

1. Builds `variant_infos: Vec<(String, Vec<ProcSig>)>` — `(variant_name, oracle signature list)`
   per discovered variant, in `package::discover_variants` order (unchanged from before this
   story).
2. Groups variant indices by structural `Vec<ProcSig>` equality, preserving first-discovery order
   across groups and within a group — the *exact same shape* as the pre-existing game-interface
   grouping a few dozen lines below in the same function (`groups.iter_mut().find(|g| ... ==
   ...)`), reused verbatim rather than reinvented.
3. Per group: emits the canonical `module type <Variant>_i = { ... procs ... }.` for the group's
   first (i.e. first-discovered) member with no comment, then — only if the group has more than
   one member — a `(* <alias1>_i, <alias2>_i, ... share <Canonical>_i's signature *)` comment,
   then one `module type <Alias>_i = { include <Canonical>_i }.` per remaining member.

Every variant still gets its own `<Variant>_i` module type name; `package.rs:419`'s
`format!("Interfaces.{callee_variant}_i")` needed **zero changes** — confirmed by grep (no hits
for `functor_params`/`build_functor_params` in this diff) and by every `Variant_*.ec`/`Comp_*.ec`
file compiling unchanged against the new `Interfaces.ec`.

Alias direction (§6, "load-bearing"): the canonical member is always the group's first-discovered
element and is always rendered before its aliases (canonical push happens before the
`group.len() > 1` branch), so `include <Canonical>_i` always refers to something already declared
earlier in the file. Verified for real: every alias-containing `Interfaces.ec` (hello-world,
kem-dem-cca-ssp, Full4WHS) compiled with `easycrypt compile -I .`.

Not touched: the pre-existing game-interface grouping loop (comps/`Iface_*`/`Adv_*`) — its own
`EcItem::ModuleType` constructions were only updated to set the new `includes: vec![]` field,
nothing about its logic or output changed. `package.rs`/`game.rs`/`proof.rs` are untouched.

### 1.3 Tests

- Two new unit tests in `interfaces.rs`:
  - `hello_world_fwd_v1_and_fwd_v2_alias_rand` — asserts the package-variant section of
    hello-world's rendered `Interfaces.ec` spells `d_UsefulOracle`'s signature exactly once, and
    that `Fwd_v1_i`/`Fwd_v2_i` render as `module type Fwd_v1_i = { include Rand_i }.` /
    `module type Fwd_v2_i = { include Rand_i }.` verbatim. (The count is scoped to the text before
    the first `module type Iface_` — a game interface coincidentally sharing an oracle name with a
    package variant is expected and, per §6, must not be deduplicated across that boundary, so a
    whole-file count would have been wrong: `Iface_MediumCompositionMoreOracles` also declares a
    `d_UsefulOracle`.)
  - `simple_4whs_no_variant_module_type_is_an_alias` — asserts Simple4WHS's rendered
    `Interfaces.ec` contains no `{ include` substring at all, i.e. this story is a confirmed no-op
    there (§4's second bullet).
- The existing `simple_4whs_interfaces_match_golden` test (golden file unchanged, no edits needed)
  is itself evidence for the same no-op claim — it would have failed had grouping produced any
  alias for Simple4WHS's 7 variants.
- `testdata/easycrypt/story04/hello-world/Interfaces.ec` was updated (regenerated from the real
  translator, then hand-verified against the panic-message diff from the first failing test run)
  to replace `Fwd_v1_i`/`Fwd_v2_i`'s two verbatim-duplicated proc blocks with the
  comment + two one-line aliases. This is the **only** golden file this story touches —
  `testdata/easycrypt/story04/4WHS/Interfaces.ec` needed no edit (test passed unchanged), and no
  other story's golden references `Interfaces.ec`'s package-variant section.

## 2. Which projects actually produced groups larger than one

| Project / theorem | Groups with >1 member | Detail |
|---|---|---|
| hello-world (`Proof`) | 1 | `Rand_i` canonical; `Fwd_v1_i`, `Fwd_v2_i` alias it (the story's own motivating example, confirmed against the real translator, not just asserted). |
| Simple4WHS | 0 | Confirmed no-op — asserted by the new test and by the unchanged golden file. All 7 variants (`Prot`, `KX`, `Prot_NoKey`, `KX_NoKeys`, `PRF`, `Prot_NoPrf`, `KX_NoPrf`) keep distinct, fully-spelled-out module types. |
| kem-dem-cca-ssp | 2 | `MOD_CCA_PKE_i` aliases `MON_CCA_PKE_i` (both 3-oracle `d_PKGEN`/`d_PKENC`/`d_PKDEC` signatures); `KEM_v2_i` aliases `KEM_v1_i` (both 3-oracle `d_KEMGEN`/`d_ENCAPS`/`d_DECAPS` signatures). Confirmed by inspecting the freshly generated `_build/easycrypt/kem_dem_cca_ssp/Interfaces.ec` and by the pre-existing `kem_dem_cca_ssp_full_tree_compiles_in_dependency_order` test passing unchanged (it recompiles the whole tree from scratch every run, so it exercises the new grouped `Interfaces.ec` for real). |
| Full4WHS | 6+ | A much bigger theorem than Simple4WHS (many more package variants: `ReductionNonce`, `ReductionCR`, `ProtNoKey` all alias `Prot_i`; `KX_v2`, `KX_v3`, `KX_nochecks_v1`, `KX_nochecks_v2`, `KX_nokey` all alias `KX_v1_i`; `ReductionMac` aliases `ProtNoKeyOnlyKid_i`; `KX_noprfkey_v2` aliases `KX_noprfkey_v1_i`; more not enumerated here). Confirmed by grep on the freshly generated `Interfaces.ec` and by `full_4whs_full_tree_compiles_in_dependency_order` passing unchanged. Not itself an acceptance-criteria target (the story's no-op claim is specifically about Simple4WHS's 7 variants), but a real, useful readability win in the larger theorem the manual translation exists for. |

hello-world's and simple-KEM-example's `Interfaces.ec` acceptance point was verified via the
**targeted unit test**, not an end-to-end `domino easycrypt` run: both projects still fail at
*export* time before any file-naming/grouping decision is reached, with the exact same
pre-existing, out-of-scope invariant-dialect gap documented in story 07 §6.2 / story 10 §3
(`unsupported SMT sort <GameState_...>`), reproduced by hand during this story
(`hello-world` → `<GameState_MediumComposition_...>`, `simple-KEM-example` → `<GameState_Prot>`).
This is unrelated to and unaffected by this story's grouping logic, which runs entirely inside
`build_interfaces_file` — downstream of where the invariant translation already fails for these
two projects.

## 3. Verification run by hand, end to end

```
cargo build --workspace
D=$PWD/target/debug/domino
```

- **hello-world**: export still fails pre-file-write with the pre-existing invariant-dialect gap
  (unchanged from story 10) — verified via the targeted test above instead, per this story's own
  fallback instruction.
- **simple-KEM-example**: same — export fails with `unsupported SMT sort <GameState_Prot>`,
  identical to before this story.
- **kem-dem-cca-ssp**: `(cd example-projects/kem-dem/kem-dem-cca-ssp && $D easycrypt --theorem
  kem_dem_cca_ssp)` → `wrote _build/easycrypt/kem_dem_cca_ssp (17 files)`. `Interfaces.ec` shows
  the two real groups from §2 above. Compiled every file in dependency order with a single `-I .`
  (`Types.ec Interfaces.ec Variant_*.ec Comp_*.ec Eq_*_Invariants.ec Eq_*.ec`): everything compiles
  (a few pre-existing "may use uninitialized local variables" warnings, unrelated to this story and
  present before it too) except the same pre-existing base-case `smt(emptyE map_empty)` gap
  (story 07 §6.1) on `Eq_Game_MON_CCA_PKE_Game_MOD_CCA_PKE_Real_KEM.ec` — reproduced identically,
  confirming this story changed nothing about that gap.
- **Simple4WHS**: `wrote _build/easycrypt/Simple4WHS (19 files)`. `Interfaces.ec` has zero
  `include` occurrences among its 7 variant module types (confirmed by `grep`) — the no-op case.
- **Full4WHS**: `wrote _build/easycrypt/Full4WHS (50 files)`. `Interfaces.ec` has multiple `include`
  aliases (§2 above).
- `cargo test --workspace` covers the actual `easycrypt compile` runs for Simple4WHS, Full4WHS and
  kem-dem-cca-ssp already (`export::tests::*_full_tree_compiles_in_dependency_order`), all green
  with this story's changes in place — i.e. the grouped/aliased `Interfaces.ec` is exercised by the
  existing test suite on every `cargo test` run, not just this session's by-hand check.

## 4. Acceptance criteria, checked against what was actually built

- [x] hello-world's `Interfaces.ec` declares the two-oracle signature once and gives `Fwd_v1_i`/
      `Fwd_v2_i` as `{ include Rand_i }` — golden file updated and diffed against the real
      translator's output; new unit test `hello_world_fwd_v1_and_fwd_v2_alias_rand` asserts it
      directly.
- [x] 4WHS's (Simple4WHS's) `Interfaces.ec` is unchanged in content: no two of its seven variants
      share a signature — the pre-existing golden test passed with zero edits, and the new
      `simple_4whs_no_variant_module_type_is_an_alias` test asserts it directly.
- [x] Every generated file still compiles with `easycrypt compile -I .`, including the game files
      that apply these functors — confirmed for kem-dem-cca-ssp by hand (§3) and for Simple4WHS/
      Full4WHS/kem-dem-cca-ssp via the existing `*_full_tree_compiles_in_dependency_order` tests,
      all green.
- [x] Grouping is by structural `Vec<ProcSig>` only, and a comment lists the group's members —
      `variant_groups` is built purely from `variant_infos[..].1 == variant_infos[..].1`
      (`Vec<ProcSig>`'s derived `PartialEq`), and every group with more than one member gets a
      `(* <alias>_i, ... share <Canonical>_i's signature *)` comment before its aliases.
- [x] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. State handed to the next story

- **AST shape**: `EcItem::ModuleType` gained `includes: Vec<String>`. Empty = plain module type
  (all pre-existing call sites). One entry + empty `procs` = pure alias, rendered on one line as
  `module type X = { include Y }.`. `render_module_type` also handles the general
  multiple-includes-plus-procs case (untested, unused) so a later story doesn't have to touch the
  renderer again if it ever needs that combination.
- **Grouping helper is not factored out into a shared function** — the story said "reuse the same
  grouping shape/helper if practical"; the shape (structural-equality grouping preserving
  first-discovery order) is copied, not extracted into a shared function, since the two call sites
  (variant grouping, composition/export grouping) sit a few dozen lines apart in the same function
  and operate on different key types (`Vec<ProcSig>` either way, but drawn from different vectors
  with different surrounding bookkeeping — `variant_infos` vs `canonical`/`comp_mangled`). If a
  future story adds a third grouping site, extracting `fn group_by_structural_key<T:
  PartialEq>(items: &[T]) -> Vec<Vec<usize>>` would be the natural move; not done here to keep this
  story's diff to exactly the two things it needed to change.
- **`package.rs:419`'s `functor_params` needed no change** — confirmed by inspection and by every
  compile test passing; a later story touching `package.rs` should still expect
  `Interfaces.<callee_variant>_i` to always exist as *either* a real declaration or an alias, and
  can keep treating it as an opaque name.
- **Full4WHS is a much richer test bed for this feature than Simple4WHS** — if a later story wants
  more than one real example of grouping beyond hello-world/kem-dem-cca-ssp, Full4WHS's
  `Interfaces.ec` already has 6+ groups (§2) and compiles clean today.
- **hello-world / simple-KEM-example's export-time invariant-dialect gap (story 07 §6.2) is exactly
  as open as before** — this story's grouping logic lives entirely inside
  `build_interfaces_file`, downstream of where those two projects already fail, so nothing here
  interacts with that gap one way or the other.

## 6. Notes for follow-up (not this story's scope)

- No new issues were found. The pre-existing base-case `smt(emptyE map_empty)` gap (story 07 §6.1)
  and the hello-world/simple-KEM-example invariant-dialect gap (story 07 §6.2) are both exactly as
  documented before this story, reproduced identically during verification, and untouched by this
  story's changes (§3, §5).
