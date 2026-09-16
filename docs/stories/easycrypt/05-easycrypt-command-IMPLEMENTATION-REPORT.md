# Story 05 — Implementation report

**Status:** done. `cargo build --workspace`, `cargo test --workspace` (292 passed, 4 pre-existing
`#[ignore]`d, none new failing) and `cargo clippy --workspace --all-targets` are all clean.
`easycrypt` (`r2026.06-12-g7e192dd`) was on `PATH`, so `simple_4whs_full_tree_compiles_in_dependency_order`
(§5 of this story, run for real) compiled `Types.ec`, `Interfaces.ec`, every `packages/*.ec` and
every `games/*.ec` for `Simple4WHS` end to end via the exact `-I` recipe below — all exit 0.

## 1. The CLI surface, exactly as shipped

```
domino easycrypt [--project <DIR>] [--theorem <NAME>] [--out <DIR>]
```

`crates/domino/src/cli.rs`: `Commands::Easycrypt(Easycrypt)`, doc-commented "Export a Domino theorem
to an EasyCrypt project." — same style as its neighbours. Note the flag is `--project`, **not**
`--path`: every *other* existing command (`Inline`, `Debug`, `Latex`, `Prove`, `Proofsteps`) uses
`--path`, but this story's own §3.1 spells the new command's flag `--project` explicitly, so that's
what got built. This is a real, intentional inconsistency across the CLI, not an oversight — flagged
here in case a later cleanup story wants to reconcile the two.

- `--project`: same semantics as every other command's project-root flag (defaults to
  `project::directory::find_project_root()`).
- `--theorem`: optional; without it, **every** theorem in the project is exported, sorted by name.
  A named theorem that doesn't exist errors via the existing `TheoremNotFound` (reused from
  `inline`), not a new type.
- `--out`: optional; defaults to `<project>/_build/easycrypt`. Always treated as the *parent*
  directory holding one subdirectory per exported theorem (`<out>/<theorem>/...`), never the
  theorem's own directory.

Wired into `main.rs`'s `easycrypt(e: &Easycrypt) -> Result<(), Error>`, matching `inline`'s
`match &e.path { Some(p) => p.clone(), None => find_project_root()? }` idiom exactly. Two new
top-level `Error` variants: `EcExport(#[from] sspverif::writers::easycrypt::EcExportError)`
(`#[diagnostic(transparent)]`) and `EcExportIo(#[from] std::io::Error)` (same shape as
`project::error::Error::IOError` — no diagnostic label, since a bare I/O failure has no span to
give one).

## 2. Library entry point, exactly as shipped

```rust
// src/writers/easycrypt/export.rs
pub struct SkipNote { pub kind: &'static str, pub left: String, pub right: String, pub reason: &'static str }

pub struct ExportedTheorem {
    pub files: BTreeMap<PathBuf, String>,       // paths relative to the theorem's own out dir
    pub skipped: Vec<SkipNote>,
    pub bits_type_names: Vec<String>,            // Types.ec bits types, emission order
    pub fn_const_names: Vec<String>,              // Types.ec fn consts, emission order (already "func_"-mangled)
    pub package_variant_names: Vec<String>,       // packages/*.ec, discovery order
    pub game_names: Vec<String>,                  // games/*.ec, discovery order
    pub randomness_mapping_oracles: usize,        // oracles across this theorem's equivalences with randomness != Custom
}

pub fn export_theorem(theorem: &Theorem<'_>) -> Result<ExportedTheorem, EcExportError>;
pub fn write_files(out_dir: &Path, files: &BTreeMap<PathBuf, String>) -> std::io::Result<()>;
```

This is a deliberate divergence from the story's own illustrative signature
(`export_theorem(theorem: &Theorem, out: &Path)`, §3.4): `out` is dropped from `export_theorem`
because nothing in it touches disk at all, and reappears as `write_files`'s own (separate) `out_dir`
parameter — "Writing is a thin wrapper" taken literally. `export_theorem` runs
`EquivalenceTransform` itself (callers pass the plain `Theorem` a `Project` hands back, exactly
what every story 02–04 builder's own tests already do), unions `GameInstAux::types` across
`auxs`, then calls `build_types_file`, `build_interfaces_file`, `compute_package_variants` and
`compute_game_files` — each exactly once, each already returning `Result<_, EcExportError>`, so no
new error type was needed beyond one addition (§3 below).

`ExportedTheorem`'s five report-only fields beyond `files`/`skipped` exist so `domino easycrypt`'s
stdout report (§4) never re-derives data by re-parsing rendered `.ec` text or re-walking `theorem`
itself — every field is something `export_theorem` already has in hand while building `files`.
`bits_type_names`/`fn_const_names` are computed by calling `typesfile::collect_bits_types`/
`collect_fn_consts` a second time (both widened `fn` → `pub(crate)` for this), mirroring story 04's
own "recomputed, not threaded through" precedent (its report §3) rather than changing
`build_types_file`'s signature.

## 3. One new `EcExportError` variant, and why two unrelated files changed with it

```rust
// src/writers/easycrypt/mod.rs
#[error(transparent)] #[diagnostic(transparent)]
Transform(#[from] crate::transforms::theorem_transforms::EquivalenceTransformError),
```

`export_theorem` runs `EquivalenceTransform` itself (§2), so its one real failure mode —
`EquivalenceTransformError::UnboundedLoop` (a sample reachable through a loop `loopunroll` couldn't
unroll) — has to fit through `EcExportError`. `EcExportError` derives `Clone, PartialEq, Eq`
(existing test code elsewhere in `types.rs`/`package.rs` asserts `EcExportError` equality via
`hard_error_expr_test!`-style macros), which transitively requires `EquivalenceTransformError` and
the `UnboundedLoopError` it wraps to implement the same three traits. Neither did before this story;
both do now (`src/transforms/theorem_transforms.rs`, `src/transforms/sample_max_counter_extractor.rs`)
— `miette::NamedSource<String>`/`SourceSpan`, their only non-trivial field types, already derive all
three, so this was a one-line addition on each, not a redesign.

Also added: `Equivalence::randomness(&self) -> &[(String, RandomnessType)]` (`src/gamehops/equivalence/mod.rs`,
`pub(crate)`, alongside the existing `randomness_by_oracle_name`) — needed to count randomness-mapping
oracles (§4) without panicking on a name lookup.

## 4. What `example-projects/yao` actually fails on (not what the story guessed)

§4's failing-export acceptance bullet suggests "a project using `Set`, e.g. `example-projects/yao`".
**`yao` does not use `Set` anywhere** (`grep -rl "Set(" example-projects/yao` is empty) — that part of
the story text is stale. What `yao`'s `Yao` and `Yao3Layer` theorems actually hit is
`EquivalenceTransformError::UnboundedLoop`: `Mod.pkg.ssp`'s `GARBLE` oracle samples inside a
`for j: 1 <= j <= w { ... }` loop whose bound `w` is not a literal, so `loopunroll` can't unroll it.
This is exactly the `Transform` variant added in §3, and it renders a full miette diagnostic with a
real source span and a `help:` — arguably a *better* demonstration of "reports a `miette` diagnostic
with a span" than a bare `UnsupportedType` would have been:

```
Error: domino::sample_max_counter::unbounded_loop
  × cannot bound the sample counter: oracle `GARBLE` samples inside a loop
  │ that `loopunroll` could not unroll
    ╭─[Mod.pkg.ssp:25:9]
 24 │             xtilde <- new Table(Integer, Bits(n));
 25 │ ╭─▶         for j: 1 <= j <= w {
    ...
```

`yao`'s other two theorems, `HybridSecurity` and `LayerSecurity`, export cleanly on their own
(confirmed by running `domino easycrypt --theorem <name>` for all four `yao` theorems individually).
This is exactly why "build every requested theorem in memory, write only if all succeeded" (§5) had
to span the *whole invocation*, not just one theorem: plain `domino easycrypt` (no `--theorem`) on
`yao` tries theorems in sorted order (`HybridSecurity`, `LayerSecurity`, `Yao`, `Yao3Layer`) and would
otherwise leave `HybridSecurity`'s and `LayerSecurity`'s directories written on disk next to a
top-level error — contradicting §4's "writes no files" for that exact project. Verified both ways:
`--theorem Yao` alone and the bare command both report the diagnostic and leave `_build/easycrypt`
absent entirely.

## 5. Directory layout and `-I` convention

Exactly §3.2, subdirectories (not flattened):

```
<out>/<theorem>/
├── Types.ec
├── Interfaces.ec
├── packages/<Variant>.ec
└── games/<Comp>.ec
```

No `Eq_*.ec`/`Eq_*_Invariants.ec` — stories 06/07's job, and nothing here creates empty placeholders
for them. `write_files` (§2) creates `packages/`/`games/` via `create_dir_all` on each file's parent,
so the subdirectory choice needed no extra code either way; flattening was never seriously considered
since story 04's own compile recipe (`00-overview.md` §7, restated in §5 of this story) already
assumes the subdirectory layout.

Compile order/flags, unchanged from story 04's own recipe and re-verified end to end by this story's
own integration test:

```bash
easycrypt compile -I <out>/<theorem> Types.ec
easycrypt compile -I <out>/<theorem> Interfaces.ec
easycrypt compile -I <out>/<theorem> -I <out>/<theorem>/packages packages/<Variant>.ec   # any order — packages don't depend on each other
easycrypt compile -I <out>/<theorem> -I <out>/<theorem>/packages -I <out>/<theorem>/games games/<Comp>.ec   # any order — games don't depend on each other either
```

**Write-then-atomicity**: `export_theorem` builds one theorem's whole `files` map in memory (§2);
`easycrypt()` in `main.rs` builds *every* requested theorem's `ExportedTheorem` first (propagating
the first error via `?`, so nothing after it even runs) and only starts calling `write_files` once
every one of them succeeded (§4 explains why this had to be invocation-wide, not per-theorem).
Confirmed byte-identical on rerun (`write_files_round_trips_and_rewriting_is_byte_identical` in
`export.rs`, plus a manual `diff -r` of two consecutive real 4WHS runs).

## 6. The stdout report, exactly as shipped

```
theorem Simple4WHS
  types       bits_n; func_mac, func_prf
  packages    7 variants (Prot, KX, Prot_NoKey, KX_NoKeys, M_PRF, Prot_NoPrf, KX_NoPrf)
  games       Hybrid0, Hybrid1, Hybrid2, PRF_Game
  skipped     1 reduction hop (Hybrid2 ~ Hybrid3): reductions are not translated
  randomness  25 oracles declare an explicit randomness mapping (not translated by this exporter)
  wrote       _build/easycrypt/Simple4WHS (13 files)
```

This is the *real* output for `Simple4WHS`, not the story's own illustrative example, which doesn't
match actual codebase state on two counts kept intentionally in this report rather than "fixed" to
match the story text: the example's file count ("7 files") is wrong — the real count is 13 (7
package variants + 4 games + `Types.ec` + `Interfaces.ec`, all independently confirmed against the
golden files under `testdata/easycrypt/story03/4WHS/` and `testdata/easycrypt/story04/4WHS/`) — and
its game list ("Hybrid0, Hybrid1, Hybrid2, PRF") omits story 04's own `_Game`-suffix escape
(`PRF_Game`, §5.1 of the story 04 report), which is real, tested, committed behavior this story
correctly inherits rather than re-litigates.

Format, one label-value line per field, `"  {:<12}{}"`:

- **`types`**: bits type names (already-mangled, e.g. `bits_n`) joined `", "`, then `"; "`, then
  `func_`-prefixed fn-const op names joined `", "` — either half may be empty (prints only the
  non-empty half, or `"(none)"` if both are).
- **`packages`**: `"<n> variant(s) (<names>)"`, discovery order (not alphabetical — matches
  `compute_package_variants`'s own order, which is first-discovery over `theorem.instances`).
- **`games`**: names only, discovery order, no count prefix.
- **`skipped`**: one line **per distinct skipped-hop kind** (`reduction`/`hybrid`/`conjecture`),
  first-seen order, grouping every pair that kind covers: `"<n> <kind> hop(s) (<left> ~ <right>, ...):
  <reason>"`. This reproduces the story's own worked example's exact wording for the single-reduction
  case (`"1 reduction hop (Hybrid2 ~ Hybrid3): reductions are not translated"`) and generalises
  correctly to multiple hops of one kind (`kem-dem-cca-ssp`: `"3 reduction hops (A ~ B, C ~ D, E ~
  F): reductions are not translated"`) — confirmed against a real project, not just imagined. Omitted
  entirely when nothing was skipped. `GameHop::Equivalence` never produces a note; `Hybrid`'s reason
  text is `"hybrid game hops are not translated"` and `Conjecture`'s is `"conjectures are not
  translated"`, but no target project's successful export exercises either — see §8.
- **`randomness`**: `"<n> oracle(s) declares/declare an explicit randomness mapping (not translated by
  this exporter)"`, counting every oracle across this theorem's equivalence hops (direct, or nested
  in a `Hybrid`'s own `Equivalence`) whose `randomness:` annotation is `simple`/`none` (i.e. not the
  default `Custom`) — `Equivalence::randomness()` (§3). **Omitted entirely when the count is 0**
  (confirmed live: `simple-KEM-example`'s report has no `randomness` line at all).
- **`wrote`**: the theorem's own output directory — printed relative to `--project` when it's a
  descendant of it (the common case; matches the story's own worked example verbatim when run from
  inside the project directory), absolute otherwise (e.g. a `--out` pointing outside the project) —
  then `"(<n> files)"`.

All formatting lives in `crates/domino/src/main.rs` (`print_easycrypt_report` and its nested
helpers), not in the library — `ExportedTheorem` carries only the facts, the CLI presents them,
matching how every other command in this binary already does its own `println!`-based reporting
(`proofsteps`/`prove` in `src/project/mod.rs`).

## 7. Which example projects export cleanly today

| Project | Theorem | Result |
|---|---|---|
| `hello-world` | `Proof` | clean (9 files; 1 skipped reduction hop; 1 randomness-mapping oracle) |
| `simple-KEM-example` | `KEM_Proof` | clean (12 files; 2 skipped reduction hops; no randomness line) |
| `kem-dem/kem-dem-cca-ssp` | `kem_dem_cca_ssp` | clean (15 files; 3 skipped reduction hops; 3 randomness-mapping oracles) |
| `4WHS` | `Simple4WHS` | clean (13 files; 1 skipped reduction hop; 25 randomness-mapping oracles) |
| `4WHS` | `Full4WHS` | clean (32 files; 5 skipped reduction hops; 102 randomness-mapping oracles) |
| `yao` | `HybridSecurity` | clean (41 files; 1 skipped reduction hop; 6 randomness-mapping oracles) — not an acceptance target, checked only to explain §4/§5's atomicity choice |
| `yao` | `LayerSecurity` | clean (14 files) — same caveat |
| `yao` | `Yao`, `Yao3Layer` | fail: `EquivalenceTransformError::UnboundedLoop` (§4) — the story's own intended negative-path target, via a different real construct than it guessed |
| `hello-world-hybrid` | `Hybrid`, `Hybrid2` | **project fails to load at all** (`DirectoryProject::load` itself errors, `ssbee::code::unproven_theorem` on `Hybrid2.ssp` — a pre-existing, unrelated project-consistency problem, not something this story's export code touches). This is the only `example-projects/*` fixture in the whole repo with a `hybrid`/`conjecture` game hop, so no target project's *successful* export exercises the `Hybrid`/`Conjecture` skip-note text in §6 — only `Reduction`'s. |

All five acceptance-target exports (§4's first bullet) re-verified by real `cargo build` + manual
`domino easycrypt` runs in this session, in addition to the golden/compile tests in
`src/writers/easycrypt/export.rs`.

## 8. State handed to the next story

- **Entry points**: `export::export_theorem(theorem: &Theorem<'_>) -> Result<ExportedTheorem, EcExportError>`;
  `export::write_files(out_dir: &Path, files: &BTreeMap<PathBuf, String>) -> std::io::Result<()>`.
  Story 07 (proof skeleton) adds `Eq_*.ec`/`Eq_*_Invariants.ec` — the natural seam is another field on
  `ExportedTheorem` (or a second map) populated the same way `files` already is, keeping
  `write_files` untouched.
- **`EcExportError::Transform`** (§3) is now the standard way any future `export_theorem`-adjacent
  code surfaces an `EquivalenceTransform` failure — don't reintroduce a second wrapping path.
- **`Equivalence::randomness()`** (§3) is `pub(crate)`, available to story 06/07 if invariant
  translation ever needs to distinguish `Custom`/`Simple`/`None` per oracle directly instead of via
  the aggregate count this story uses.
- **No `Hybrid`/`Conjecture` skip-note has ever been exercised against a real, successfully-exporting
  project** (§7) — the code path exists and is unit-reachable (`export.rs`'s `skip_kind_and_reason`
  matches all four `GameHop` variants), but if a future story adds a hybrid-hop-bearing fixture that
  actually loads, re-verify the exact wording live rather than trusting this report's untested guess.
- **`hello-world-hybrid` is broken independent of this epic** — flagged here so a future session
  doesn't waste time assuming a story-05 regression when it hits the same `unproven_theorem` error.
