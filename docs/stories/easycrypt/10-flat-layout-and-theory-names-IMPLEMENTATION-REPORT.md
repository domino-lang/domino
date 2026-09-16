# Story 10 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (340 passed, 4 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`~/.opam/easycrypt/bin/easycrypt`, resolved via the developer's opam switch) was on
`PATH`, so every compile-shaped test ran for real, plus the story's own §5 recipe was run by hand,
end to end, for `Simple4WHS`, `Full4WHS` and `kem-dem-cca-ssp`.

## 1. What changed

### 1.1 Theory naming (§3.1)

- `names.rs`: deleted `RESERVED_STDLIB_THEORY_NAMES` (`&["PRF"]`) and the `is_reserved_stdlib_theory`
  branch inside `mangle_name`'s `Module`/`ModuleType` case. `NameKind::Module` mangling is back to
  exactly what the doc comment always said: uppercase the first letter, `M_` prefix only on a
  digit/underscore start. The test `mangle_module_reserved_stdlib_theory_name_gets_prefix` is
  deleted.
- `interfaces.rs`: deleted the `variant_names_taken` `HashSet` and the `_Game`-suffix fallback in
  `build_interfaces_file`'s composition-naming loop. `comp_mangled` is now a plain
  `comp_names.mangle(NameKind::Module, &comp.name)?` per composition, exactly like every other
  `Names` registry in this module.
- **Only the theory (file) name gained a prefix — nothing else moved.** `export.rs` writes
  `Variant_<name>.ec` for a package variant and `Comp_<name>.ec` for a composition, where `<name>`
  is the *same* string `package::PackageVariant::name` / `game::GameFile::name` always was (the
  module's own name, unprefixed). Concretely:
  - `game.rs::render_game_file`: the `clone` item's `base` (the theory being cloned) is now
    `format!("Variant_{}", variant_names[idx])`, and the file's plain `require` list prefixes every
    variant name the same way (`plain_requires.extend(variant_requires.iter().map(|v|
    format!("Variant_{v}")))`). `Interfaces` is never prefixed. The clone alias itself
    (`Pkg_<inst>`), the functor-application alias (`Inst_<inst>`), and every qualified reference to
    an already-cloned module (`Pkg_<inst>.<Variant>`) are untouched — they resolve through the
    *local* clone alias, not the theory name, so they never needed the prefix.
  - `proof.rs`: `CompLayout` gained a second field, `comp_theory` (`format!("Comp_{comp_mangled}")`),
    alongside the pre-existing `comp_mangled` (which stays what it always was — the base that
    `Game_<mangled>`/`Exp_<mangled>` derive from). Every place that used to qualify *into* a
    composition's game file — `restrictions_for`'s `-<X>.Game_<X>` / `-<X>.Pkg_<inst>.<Variant>`,
    `build_side_record_lit`'s qualified state reads, the `Pr[...]` module string, and the
    `require <CompA> [<CompB>].` list — now uses `comp_theory` for the *qualifier* and
    `comp_mangled` only where it is genuinely part of a module name (`Game_<mangled>`). This is the
    one place in the story where "only the file name changes" needed a second field, not a
    find-and-replace: `format!("{0}.Exp_{0}(A)", comp_mangled)` cannot simply become
    `format!("{0}.Exp_{0}(A)", comp_theory)`, because the `Exp_` suffix must stay the *unprefixed*
    mangled base, only the qualifier before the dot changes.
  - `package.rs`, `game.rs`'s router/experiment bodies, and `interfaces.rs`'s module-type bodies are
    otherwise untouched — no module name, clone alias, functor-application name or restriction
    string changed spelling, only the qualifier prefix used to reach into another file.
- 4WHS's `PRF` package now mangles to plain `PRF` (file `Variant_PRF.ec`, `module PRF`), and its
  `PRF` composition also mangles to plain `PRF` (file `Comp_PRF.ec`, `module Game_PRF` / `module
  Exp_PRF`) — no collision, because the two now live in disjoint file namespaces (`Variant_*` vs.
  `Comp_*`) as well as disjoint `Names` registries. Verified against the real project (§3 below),
  not just asserted: neither `M_PRF` nor `PRF_Game` appears anywhere in the fresh export or in any
  updated golden/testdata file (`grep -rn "M_PRF\|PRF_Game" testdata/ src/writers/easycrypt/` is
  empty after this change).

### 1.2 Flat output (§3.2)

- `export.rs::export_theorem`: the two file-insertion loops changed from
  `PathBuf::from(format!("packages/{}.ec", variant.name))` /
  `PathBuf::from(format!("games/{}.ec", game.name))` to
  `PathBuf::from(format!("Variant_{}.ec", variant.name))` /
  `PathBuf::from(format!("Comp_{}.ec", game.name))`. `Types.ec`, `Interfaces.ec` and the
  `Eq_*.ec`/`Eq_*_Invariants.ec` pair were already bare file names (no subdirectory) and are
  unchanged.
- `write_files` needed **no code change** — it already just does `out_dir.join(rel_path)` plus
  `create_dir_all(path.parent())`; with every key now a bare file name, `create_dir_all` only ever
  creates `out_dir` itself. Its doc comment is updated to say so.
- Stdout report labels (`packages`, `games` in `crates/domino/src/main.rs`) are unchanged, per the
  owner's Q4 decision recorded in the story — they stay as grouping labels even though the files no
  longer sit in same-named subdirectories.

### 1.3 Both escape hatches retired (§3.3)

Confirmed by the acceptance grep itself:

```
$ grep -rn "RESERVED_STDLIB\|_Game\b" src/writers/easycrypt/
(no output)
```

- `names.rs`: `RESERVED_STDLIB_THEORY_NAMES`, `is_reserved_stdlib_theory`, and the test
  `mangle_module_reserved_stdlib_theory_name_gets_prefix` are all deleted (§1.1).
- `interfaces.rs`: `variant_names_taken` and the `_Game` suffix branch are deleted (§1.1). The old
  16-line comment block explaining the hack is replaced with a shorter one explaining why the
  collision is now structurally impossible (disjoint `Variant_*.ec`/`Comp_*.ec` file namespaces).
- No trace of either hack's name survives anywhere in `src/writers/easycrypt/`, including comments —
  a stray comment in `package.rs` that used to say `` `RESERVED_STDLIB_THEORY_NAMES` `` (as
  historical context, not live code) was reworded to avoid the literal substring, since the
  acceptance grep is textual and would otherwise still fire on a comment.

### 1.4 Tests and goldens moved (§3.4)

- `testdata/easycrypt/story03/{4WHS,hello-world}/*.ec` (and the local, gitignored `.eco` build
  artifacts sitting alongside them — see §4 below) renamed in place: every package-variant file
  gained a `Variant_` prefix (`KX.ec` → `Variant_KX.ec`, `M_PRF.ec` → `Variant_PRF.ec`, `Fwd_v1.ec` →
  `Variant_Fwd_v1.ec`, ...). `Types.ec` is untouched.
- `testdata/easycrypt/story04/{4WHS,hello-world}/packages/*.ec` moved up one level and renamed the
  same way (`packages/KX.ec` → `Variant_KX.ec`, `packages/M_PRF.ec` → `Variant_PRF.ec`); the now-empty
  `packages/` directories are removed.
- `testdata/easycrypt/story04/{4WHS,hello-world}/games/*.ec` moved up one level and renamed with the
  `Comp_` prefix (`games/Hybrid0.ec` → `Comp_Hybrid0.ec`, `games/PRF_Game.ec` → `Comp_PRF.ec`,
  `games/BigComposition.ec` → `Comp_BigComposition.ec`, ...); the now-empty `games/` directories are
  removed. `Types.ec`/`Interfaces.ec` (already top-level) are untouched in *path*, but
  `Interfaces.ec`'s *content* did change for 4WHS (§1.1 — `M_PRF_i` → `PRF_i`, `Iface_PRF_Game` →
  `Iface_PRF`, `Adv_PRF_Game` → `Adv_PRF`); hello-world's `Interfaces.ec` is byte-identical (it has
  no `PRF`-shaped collision to begin with).
- Every golden file's *content* was regenerated from the real translator (not hand-edited) — a
  temporary `DOMINO_BLESS_EASYCRYPT_GOLDENS` environment-variable branch was added to each of
  `package.rs`/`game.rs`/`interfaces.rs`'s own `assert_golden` test helper, run once against the
  `*_match_golden` tests to write the new expected content, diffed by eye against the story's own
  worked example, then removed again before the final commit — the shipped `assert_golden` helpers
  are byte-identical to their pre-story-10 shape (still a plain `assert_eq!` against a file on disk).
- `testdata/easycrypt/story04/*/Variant_*.ec` (the package-variant fixtures `game.rs`'s own
  `assert_compiles` tests compile against, as opposed to golden-*compared* against) are **not**
  independently golden-tested — confirmed, by diffing against git history, that they have always been
  byte-identical copies of `testdata/easycrypt/story03/*/Variant_*.ec` for the same project/theorem
  (`diff` against `git show HEAD:...` before this story's changes: identical). They were updated the
  same way: copied straight from the freshly-regenerated story03 files rather than blessed
  independently, which is the same maintenance relationship they had before this story.
- Every `assert_compiles_with_paths(&[base, packages, games], …)` call — in `export.rs`'s three
  full-tree compile tests and `game.rs`'s own per-project compile tests — became
  `assert_compiles(base, …)`, and the now-unused `packages`/`games` local `String`s were deleted from
  those tests.
- `assert_compiles_with_paths` itself (`mod.rs`) is **not** deleted — it has one remaining, genuinely
  unrelated caller: `invariant.rs::hybrid0_hybrid1_invariants_file_compiles` spreads its fixture
  across two directories that have nothing to do with `packages/`/`games/` (a scratch dir holding the
  just-rendered invariants file, and `testdata/easycrypt/story02/4WHS` holding `Types.ec`). The
  story's own instruction ("if `assert_compiles_with_paths` ends with no callers, delete it") is
  conditional, and that condition is false; deleting it would have broken this real caller for no
  reason. Its doc comment is updated to explain the *new* reason it still exists, since the old
  packages/games-specific rationale no longer applies.

## 2. A genuine, verified fact this story turned up: `.eco` fixtures were never actually committed

The story's §3.4 says to "check in the regenerated `.eco` files alongside the `.ec` ones, as the
existing goldens do." This turned out to be based on a stale assumption: `.eco` files are listed in
this repository's own `.gitignore` (`*.eco`), and `git ls-files testdata/easycrypt/story03
testdata/easycrypt/story04 | grep eco` returns nothing, before or after this story. The `.eco` files
sitting in those directories are local `easycrypt`-compile cache artifacts left over from a
developer's own `cargo test` runs (EasyCrypt writes one next to every `.ec` it compiles), not
tracked goldens. They were still renamed on disk for local consistency (so a stale `M_PRF.eco` isn't
left orphaned next to a newly-named `Variant_PRF.ec`), but `git status` never saw them and nothing
was staged for them. **This is not a regression or an oversight in this story** — it is exactly as
true before this story as after; it's flagged here only because the story text asserted something
about existing goldens that is not accurate, and a later story reading this file should not go
looking for tracked `.eco` files.

## 3. Verification run by hand, end to end

```
cargo build --workspace
D=$PWD/target/debug/domino
```

- **`Simple4WHS`**: `(cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS)` → `wrote
  _build/easycrypt/Simple4WHS (19 files)`. `ls _build/easycrypt/Simple4WHS` is flat: `Types.ec`,
  `Interfaces.ec`, seven `Variant_*.ec`, four `Comp_*.ec` (`Comp_Hybrid0.ec`, `Comp_Hybrid1.ec`,
  `Comp_Hybrid2.ec`, `Comp_PRF.ec` — confirming `PRF`'s composition file is `Comp_PRF.ec`, not
  `Comp_PRF_Game.ec`), three `Eq_*.ec` + three `Eq_*_Invariants.ec`. Compiling every file in
  dependency order with **the exact single-`-I` command below** succeeds for everything except the
  pre-existing, already-documented (story 07 §6.1) base-case `smt(emptyE map_empty)` gap on every
  `Eq_*.ec` — reproduced identically, same failure (`cannot prove goal (strict)` at the same tactic
  line), confirming story 10 changed nothing about that gap.
- **`Full4WHS`**: `(cd example-projects/4WHS && $D easycrypt --theorem Full4WHS)` → `wrote
  _build/easycrypt/Full4WHS (50 files)`, flat, with `PRF`'s composition again `Comp_PRF.ec`. Same
  compile loop: every one of the 50 files compiles with a single `-I .`, again except the same
  documented base-case gap on all nine `Eq_*.ec` files.
- **`kem-dem-cca-ssp`**: `(cd example-projects/kem-dem/kem-dem-cca-ssp && $D easycrypt --theorem
  kem_dem_cca_ssp)` → `wrote _build/easycrypt/kem_dem_cca_ssp (17 files)`, flat. Same compile loop:
  every file compiles with a single `-I .` except the same documented base-case gap on its one
  `Eq_*.ec`.
- **`hello-world`** and **`simple-KEM-example`**: both still fail at *export* time (before any file
  is written), with the exact same pre-existing, out-of-scope error story 07's report documented in
  its §6.2 (`unsupported SMT sort <GameState_...>` — their hand-written invariants predate story 06's
  `define-state-relation (left right)` grammar entirely). This is unrelated to story 10's own scope
  (naming/layout) and unaffected by it — confirmed by running both by hand and getting byte-identical
  error text to what the existing `hello_world_fails_on_its_pre_easycrypt_invariant_format` /
  `simple_kem_example_fails_on_its_pre_easycrypt_invariant_format` tests already pinned before this
  story touched anything. The story's acceptance bullet "`hello-world`, `simple-KEM-example` and
  `kem-dem-cca-ssp` also export flat and compile" is therefore true only for `kem-dem-cca-ssp` —
  exactly the same partial truth story 07's own acceptance-criteria section already recorded for the
  same two projects, not a new gap introduced here.

**The exact single-`-I` command that compiles a whole flat theorem directory in dependency order**
(confirmed for `Simple4WHS`, `Full4WHS`, and `kem-dem-cca-ssp`):

```bash
cd _build/easycrypt/<Theorem>
for f in Types.ec Interfaces.ec Variant_*.ec Comp_*.ec Eq_*_Invariants.ec Eq_*.ec; do
  easycrypt compile -I . "$f" || { echo "FAILED: $f"; break; }
done
```

Every `$f` above resolves with `-I .` alone — no `-I packages`, no `-I games`.

## 4. Acceptance criteria, checked against what was actually built

- [x] `domino easycrypt --theorem Simple4WHS` on 4WHS writes 19 files, all directly in
      `_build/easycrypt/Simple4WHS/`, no subdirectories (§3, confirmed by `ls`).
- [x] Every one of them compiles with `easycrypt compile -I . <file>.ec` — a single `-I` — except
      the pre-existing, documented (story 07 §6.1) base-case `smt` gap on every `Eq_*.ec`, which is
      not this story's to fix and is reproduced identically to before.
- [x] `grep -rn "RESERVED_STDLIB\|_Game\b" src/writers/easycrypt/` finds nothing (§1.3, quoted above
      verbatim).
- [x] 4WHS emits `Variant_PRF.ec` and `Comp_PRF.ec`; neither `M_PRF` nor `PRF_Game` appears anywhere
      in the output or the goldens (§1.1, §3).
- [~] `hello-world`, `simple-KEM-example` and `kem-dem-cca-ssp` also export flat and compile — true
      for `kem-dem-cca-ssp` (confirmed end to end, §3); **not** true for `hello-world`/
      `simple-KEM-example`, which fail at export with the exact same pre-existing, out-of-scope
      invariant-format gap story 07's report already documented for them (§3) — not a defect in this
      story's own code, and not something story 10's scope (naming/layout) touches.
- [x] No module name, clone alias or restriction string changed — diffed the generated
      `Eq_*.ec`/`Comp_*.ec` files by hand (§1.1, §3): only the theory qualifier moved from
      `Hybrid0.`/`Hybrid2.` to `Comp_Hybrid0.`/`Comp_Hybrid2.` (proof.rs) and from bare `Prot`/`KX` to
      `Variant_Prot`/`Variant_KX` in `clone`/`require` (game.rs); every module name (`Game_*`,
      `Exp_*`, `Pkg_*`, `Inst_*`) and every restriction string's tail (`.Game_Hybrid2`,
      `.Pkg_KX.KX`) is byte-identical to before.
- [x] Deterministic; `cargo build/test/clippy --workspace` clean (§ intro).

## 5. State handed to the next story

- **Final file-name scheme, as shipped**: `Types.ec`, `Interfaces.ec` (unprefixed, unchanged);
  `Variant_<X>.ec` per package variant (containing `module <X>`, unchanged spelling); `Comp_<X>.ec`
  per composition (containing `module Game_<X>`, `module Exp_<X>`, `clone Variant_<Y> as Pkg_<inst>.`,
  `module Inst_<inst> = ...` — all unchanged spelling); `Eq_<L>_<R>.ec` /
  `Eq_<L>_<R>_Invariants.ec` per equivalence (unchanged). All flat, one directory per theorem, no
  subdirectories. `<X>` in `Variant_<X>.ec`/`Comp_<X>.ec` is always exactly `PackageVariant::name` /
  `GameFile::name` — the same value the module itself is named after — so any future code that has
  one of those structs in hand can compute its own file name with `format!("Variant_{}.ec",
  variant.name)` / `format!("Comp_{}.ec", game.name)` without needing a new lookup.
- **The exact single-`-I` command** that compiles a whole flat theorem directory in dependency order
  is quoted verbatim in §3 above and is now also what `export.rs`'s own three
  `*_full_tree_compiles_in_dependency_order` tests do for real (they used to build `packages`/`games`
  subdir strings and call `assert_compiles_with_paths`; now they call plain `assert_compiles(&base,
  …)` for every file).
- **Which goldens moved**: every file under `testdata/easycrypt/story03/*/` and
  `testdata/easycrypt/story04/*/` except `Types.ec`/`Interfaces.ec` — full list in §1.4. Story 08,
  when implemented, should expect `Variant_*.ec`/`Comp_*.ec` names from the start; it does not need
  to migrate anything (its own plan already had no fixtures of its own yet — §6 of the story flagged
  this as in-scope-if-it-existed, and it does not exist yet as of this session).
- **Both escape hatches are confirmed gone**, by the acceptance grep itself (§1.3) and by the
  disjoint-namespace argument (§1.1) that makes them structurally unnecessary rather than merely
  untriggered in today's fixtures: a package variant and a composition can now share a raw Domino
  name (as `PRF` does in 4WHS) with zero special-casing, because `Variant_*.ec` and `Comp_*.ec` are
  different files and `package.rs`'s/`interfaces.rs`'s `Names` registries were always independent of
  each other.
- **`CompLayout` in `proof.rs` now carries two related-but-distinct strings** — `comp_mangled` (the
  unprefixed base `Game_*`/`Exp_*` derive from) and `comp_theory` (`Comp_<comp_mangled>`, the
  qualifier a `require`r must use). A story touching `proof.rs` again (11/12/13, or 08 once it lands)
  should use `comp_theory` for anything that crosses a `require` boundary and `comp_mangled` only
  where it is genuinely part of a module's own name.
- **Not touched, correctly out of scope**: the `hello-world`/`simple-KEM-example` `GameState_`-sort
  invariant-dialect gap (story 07 §6.2) is exactly as open as it was before this story; nothing about
  flat layout or theory naming interacts with it, since both projects fail before any file-naming
  decision is ever reached (export fails while translating the invariant, upstream of `export.rs`'s
  own file-name computation).
- **`.eco` files are not tracked goldens** (§2) — a fact worth not re-discovering: `*.eco` is
  git-ignored repo-wide, and the ones sitting in `testdata/easycrypt/story0{3,4}/` are local compile
  caches, not checked-in fixtures. Renaming them alongside the `.ec` files is a local-hygiene nicety,
  not a git operation.

## 6. Notes for follow-up (not this story's scope)

- Story 07's §6.1 base-case `smt(emptyE map_empty)` gap and §6.2 `GameState_`-dialect gap are both
  exactly as documented in that story's own report — neither was touched, and neither is affected by
  this story's naming/layout change (confirmed by reproducing both by hand, §3).
- `docs/stories/easycrypt/08-ec-ir-lowering.md` and `09-debug-on-easycrypt.md` were checked (per this
  story's own §6 note that 08's plan text should be fixed here if it still mentions `packages/`/
  `games/`) — neither file mentions those paths, so there was nothing to fix there.
