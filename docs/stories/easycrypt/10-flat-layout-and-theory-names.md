# Story 10 — Flat project layout and collision-free theory names

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** stories 03–07 (all implemented).
**Blocks:** nothing, but **do this before stories 11–13**: it moves every golden file, and doing it
first keeps the other three stories to content-only diffs.

---

## 1. Why this story exists

Two problems, one cause.

**The output is not flat.** `domino easycrypt` writes `packages/*.ec` and `games/*.ec`
(`src/writers/easycrypt/export.rs:188`, `:194`). EasyCrypt resolves `require X.` by searching the
`-I` path for `X.ec`, so every consumer needs three flags:

```bash
easycrypt compile -I . -I packages -I games <file>.ec
```

The owner wants one directory and one `-I`. Verified: moving all 19 exported files of 4WHS
`Simple4WHS` into one directory and compiling with `-I .` alone works unchanged.

**Theory names are patched by hand where they collide.** There are two separate escape hatches in
the tree today, both discovered by exporting 4WHS:

- `RESERVED_STDLIB_THEORY_NAMES: &[&str] = &["PRF"]` (`src/writers/easycrypt/names.rs:189`) — a
  literal, hardcoded, one-element list. 4WHS's `PRF` package would emit `PRF.ec`, and
  `require PRF.` then resolves to EasyCrypt's own `theories/crypto/PRF.eca` instead. The package
  variant is renamed `M_PRF` to dodge it.
- A `_Game` suffix in `src/writers/easycrypt/interfaces.rs:170-181` — 4WHS's `PRF` *composition*
  collides with the `PRF` *package* in the same way, and gets renamed `PRF_Game`.

Both are symptoms of generated theory names living in the same flat namespace as the EasyCrypt
standard library and as each other. Going flat makes that namespace *smaller*, not larger, so the
fix has to come with it.

The owner's decision (Q3): **prefix every generated package and game theory unconditionally**, so a
generated theory can never be spelled like a stdlib one or like each other, and delete both hacks.
`Types.ec` and `Interfaces.ec` stay unprefixed.

## 2. Inherited from earlier stories

- Story 03 emits one theory per **package variant**, file `packages/<Variant>.ec`, containing a
  single `module <Variant>`.
- Story 04 emits one theory per **composition**, file `games/<Comp>.ec`, containing
  `clone <Variant> as Pkg_<inst>.`, `module Inst_<inst> = Pkg_<inst>.<Variant>(…)`,
  `module Game_<Comp>`, and `module Exp_<Comp>`.
- Story 04 also owns `InterfacesOutput::comp_mangled` (`interfaces.rs:38`) — the single place a
  composition's base name is computed; `Game_<X>`, `Exp_<X>` and `games/<X>.ec` all derive from it.
  The `_Game` hack lives there.
- Story 07's `Eq_*.ec` references both by qualified name: `require Hybrid0 Hybrid1.`,
  `Pr[Hybrid0.Exp_Hybrid0(A).run(…)]`, and restriction strings
  `-Hybrid0.Game_Hybrid0`, `-Hybrid0.Pkg_KX.KX`.
- Test helpers: `test_support::assert_compiles(dir, file)` and
  `assert_compiles_with_paths(&[dirs], file)` (`src/writers/easycrypt/mod.rs:42`, `:50`). The
  multi-dir form exists *only* to pass `-I packages -I games`; after this story it should have no
  callers left.

## 3. Work to do

### 3.1 The naming scheme

| Emitted theory | File (flat) | Modules inside |
|---|---|---|
| package variant | `Variant_<X>.ec` | `module <X>` (unchanged) |
| composition | `Comp_<X>.ec` | `Game_<X>`, `Exp_<X>`, `Pkg_<inst>`, `Inst_<inst>` (all unchanged) |
| shared types | `Types.ec` | unchanged |
| interfaces | `Interfaces.ec` | unchanged |
| equivalence | `Eq_<L>_<R>.ec`, `Eq_<L>_<R>_Invariants.ec` | unchanged |

**Only the theory (file) name changes.** Every module name, clone alias, functor-application name
and restriction string keeps its current spelling. That is the point of the `Variant_`/`Comp_`
choice: `Pkg_<inst>` remains free as a clone alias, so `Inst_<inst>` does not have to move either.

`Variant_` and `Comp_` are this epic's own vocabulary — see `CONTEXT.md`'s **Package variant** and
**Composition** entries.

The resulting game file:

```
require import AllCore Distr FMap Int IntDiv Types.
require Interfaces Variant_Prot Variant_KX.

clone Variant_Prot as Pkg_Prot.
clone Variant_KX   as Pkg_KX.

module Inst_KX = Pkg_KX.KX(Pkg_Prot.Prot).

module Game_Hybrid0 : Interfaces.Iface_Hybrid0 = { … }
module Exp_Hybrid0 (A : Interfaces.Adv_Hybrid0) = { … }
```

and the proof file:

```
require Comp_Hybrid0 Comp_Hybrid1.
…
declare module A <: Interfaces.Adv_Hybrid0 { -Comp_Hybrid0.Game_Hybrid0, -Comp_Hybrid0.Pkg_KX.KX, … }.
lemma … : Pr[Comp_Hybrid0.Exp_Hybrid0(A).run(b) @ &m : res] = …
```

**Verified against r2026.06-12-g7e192dd** (the exact scheme, with a module deliberately named `PRF`
inside `Variant_PRF`, cloned in `Comp_PRF`, and `Pr[Comp_PRF.Exp_PRF.run()]` used from a third
file): compiles with `-I .` only. A *module* named `PRF` never collides with
`theories/crypto/PRF.eca` — only a top-level theory can, and after this story none is spelled `PRF`.

**Also verified: the collision is real if you take the shortcut.** Naming the package theory
`Pkg_KX` and keeping `clone Pkg_KX as Pkg_KX.` fails with `the symbol Pkg_KX already exists`. A
clone alias and the theory it clones cannot share a name — this is why the theory prefix must be
something other than `Pkg_`.

### 3.2 Flat output

`export.rs` builds a `BTreeMap<PathBuf, String>` of relative paths (`:74`, `:181-207`). Drop the
`packages/` and `games/` path components; every key becomes a bare file name. `write_files`
(`:238`) keeps its `create_dir_all` for the theorem directory itself.

Stdout keeps its current shape — `packages 7 variants (…)` and `games Hybrid0, …` stay as grouping
*labels* even though the files no longer sit in those directories (owner's decision, Q4).

### 3.3 Retire both hacks

- Delete `RESERVED_STDLIB_THEORY_NAMES` and the `is_reserved_stdlib_theory` branch
  (`names.rs:189`, `:290-295`), and the test `mangle_module_reserved_stdlib_theory_name_gets_prefix`
  (`names.rs:413-420`). `NameKind::Module` mangling goes back to: uppercase first letter, `M_`
  prefix only on a digit/underscore start.
- Delete the `_Game` suffix escape in `interfaces.rs:170-181` and the `variant_names_taken` set that
  feeds it. Package-variant and composition names no longer share a namespace, because the theories
  they produce are `Variant_*` and `Comp_*`.
- 4WHS's names come back to their Domino spellings: variant `PRF` (file `Variant_PRF.ec`),
  composition `PRF` (file `Comp_PRF.ec`, modules `Game_PRF` / `Exp_PRF`).

### 3.4 Tests

- Move `testdata/easycrypt/story04/*/packages/` and `.../games/` contents up one level and rename to
  `Variant_*.ec` / `Comp_*.ec`. Same for story 03's `testdata/easycrypt/story03/*/`, whose file
  names are golden-compared.
- `M_PRF.ec` → `Variant_PRF.ec`; `PRF_Game.ec` → `Comp_PRF.ec`.
- Every `assert_compiles_with_paths(&[base, packages, games], …)` call becomes
  `assert_compiles(base, …)`. If `assert_compiles_with_paths` ends with no callers, delete it and
  the doc comment at `mod.rs:46-49` that explains why it existed.
- Check in the regenerated `.eco` files alongside the `.ec` ones, as the existing goldens do.

## 4. Acceptance criteria

- [ ] `domino easycrypt --theorem Simple4WHS` on 4WHS writes 19 files, all directly in
      `_build/easycrypt/Simple4WHS/`, no subdirectories.
- [ ] Every one of them compiles with `easycrypt compile -I . <file>.ec` — a single `-I`.
- [ ] `grep -rn "RESERVED_STDLIB\|_Game\b" src/writers/easycrypt/` finds nothing.
- [ ] 4WHS emits `Variant_PRF.ec` and `Comp_PRF.ec`; neither `M_PRF` nor `PRF_Game` appears
      anywhere in the output or the goldens.
- [ ] `hello-world`, `simple-KEM-example` and `kem-dem-cca-ssp` also export flat and compile.
- [ ] No module name, clone alias or restriction string changed — diff the generated
      `Eq_*.ec` and confirm only the theory qualifier moved from `Hybrid0.` to `Comp_Hybrid0.`.
- [ ] Deterministic; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
cd _build/easycrypt/Simple4WHS
ls                                        # flat: no packages/ or games/
for f in Types.ec Interfaces.ec Variant_*.ec Comp_*.ec Eq_*_Invariants.ec Eq_*.ec; do
  easycrypt compile -I . "$f" || { echo "FAILED: $f"; break; }
done
```

> `domino easycrypt` on 4WHS is allowed; `domino prove`/`debug` on 4WHS is not.

## 6. Notes / risks

- **`require` order still matters.** Flat does not make EasyCrypt order-insensitive; the loop above
  compiles in dependency order on purpose. Keep it.
- **Do not prefix `Types`/`Interfaces`.** The owner decided against it (Q3). If a future project
  ever collides there, that is a new story, not a reason to widen this one.
- **Do not reintroduce a stdlib name list.** If a generated `Variant_*`/`Comp_*` theory somehow
  still collides, that is a genuine new fact — record it in the implementation report with the exact
  `easycrypt` error, do not paper over it with a second list.
- **Story 08's plan mentions `packages/` and `games/`.** If it does after this lands, fix the paths
  there too — that is in scope for this story, since 08 is not yet implemented.

## 7. State handed to the next story

Record in `10-…-IMPLEMENTATION-REPORT.md`: the final file-name scheme as shipped, the exact
single-`-I` command that compiles the whole theorem, which goldens moved, and confirmation that both
escape hatches are gone.
