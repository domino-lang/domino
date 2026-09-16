# Story 05 — `domino easycrypt`: the command and the project layout

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 04 (and through it 01–03).
**Blocks:** 07.

---

## 1. Why this story exists

Stories 01–04 build ASTs in memory. This one makes them a project on disk behind a real command,
and completes the walking skeleton: after this story, `domino easycrypt` on 4WHS produces types,
interfaces, packages and games that compile under `easycrypt compile`.

## 2. Inherited from earlier stories

- Story 02: `Types.ec` builder; story 04: `Interfaces.ec`, `packages/*.ec`, `games/*.ec` builders
  and their naming. Read both implementation reports.
- The export pipeline is the existing `EquivalenceTransform`
  (`src/transforms/theorem_transforms.rs:41`, `run_treeify = true`), whose `Aux` is
  `Vec<(String, GameInstAux)>` keyed by game-instance name and carries `types: HashSet<Type>`,
  which story 02 needs.

### 2.1 How the existing commands are wired

- `crates/domino/src/cli.rs`, `enum Commands` (`:35`): `Latex`, `Prove`, `Format`, `Proofsteps`,
  `Debug`, `Inline`. Each variant has a `#[derive(clap::Args)]` struct with a `--project` option
  documented as "Path to the Domino project. Defaults to searching the current directory and its
  ancestors for an `ssp.toml`".
- Projects load through `DirectoryProject::load(root_dir, &files)` and
  `DirectoryFiles::load(root)`, with `find_project_root()` (`src/project/directory.rs:21`, `:70`,
  `:119`). Follow exactly what `Inline` does in `crates/domino/src/main.rs` — do not invent a
  second loading path.
- A theorem's hops are `Theorem::game_hops: Vec<GameHop>`; `GameHop::as_equivalence() ->
  Option<&Equivalence>`, and `Equivalence` exposes `theorem_name()`, `left_name()`, `right_name()`,
  `invariants() -> &[String]` and `trees() -> &[(String, Vec<Claim>)]` (oracle name → claims).

## 3. Work to do

### 3.1 The command

```
domino easycrypt [--project <DIR>] [--theorem <NAME>] [--out <DIR>]
```

- `--theorem` optional; without it, export **every** theorem in the project.
- `--out` defaults to `<project>/_build/easycrypt`.
- Add `Easycrypt(Easycrypt)` to `Commands` with the same doc-comment style as its neighbours
  ("Export a Domino theorem to an EasyCrypt project.").

### 3.2 Layout written per theorem

```
<out>/<theorem>/
├── Types.ec
├── Interfaces.ec
├── packages/<Variant>.ec
└── games/<Comp>.ec
```

`Eq_*.ec` and `Eq_*_Invariants.ec` arrive in stories 06 and 07; leave the directory shape ready but
do not create empty files.

Write files only after the whole theorem has been built successfully — a failed export must not
leave a half-written tree. Build everything in memory, then write.

### 3.3 What the command prints

On stdout, concise and deterministic:

```
theorem Simple4WHS
  types       bits_n; func_prf, func_mac
  packages    4 variants (KX, Prot, KX_NoKeys, Prot_NoKey)
  games       Hybrid0, Hybrid1, Hybrid2, PRF
  skipped     1 reduction hop (Hybrid2 ~ Hybrid3): reductions are not translated
  wrote       _build/easycrypt/Simple4WHS (7 files)
```

Every skipped hop is named with its kind and the reason. Randomness mappings are mentioned once per
theorem if any exist. Errors go through `miette` with the source span, like the rest of the CLI.

### 3.4 Library entry point

One function the CLI calls and tests call directly, e.g.

```rust
pub fn export_theorem(theorem: &Theorem, out: &Path) -> Result<ExportedTheorem, EcExportError>;
pub struct ExportedTheorem { pub files: BTreeMap<PathBuf, String>, pub skipped: Vec<SkipNote> }
```

Returning the file map (rather than writing inside) is what lets golden tests avoid touching disk.
Writing is a thin wrapper.

## 4. Acceptance criteria

- [ ] `domino easycrypt` runs on `example-projects/hello-world`,
      `example-projects/simple-KEM-example`, `example-projects/kem-dem/kem-dem-cca-ssp` and
      `example-projects/4WHS` (both theorems) without error.
- [ ] For 4WHS `Simple4WHS`, every generated file compiles in dependency order:
      `Types.ec`, `Interfaces.ec`, `packages/*.ec`, `games/*.ec`. Add this as an integration test
      that **skips** when `easycrypt` is not on `PATH`.
- [ ] Re-running the command produces byte-identical files.
- [ ] A failing export (point it at a project using `Set`, e.g. `example-projects/yao` — export
      only, no proving) reports a `miette` diagnostic with a span and writes **no** files.
- [ ] `--theorem Full4WHS` exports only that theorem.
- [ ] Skipped reduction/hybrid hops are listed on stdout.
- [ ] `cargo build/test/clippy --workspace` clean; `scripts/test-known-examples.sh` unaffected.

## 5. How to verify

```bash
cargo build --workspace
D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --theorem Simple4WHS
cd _build/easycrypt/Simple4WHS
easycrypt compile -I . Types.ec && easycrypt compile -I . Interfaces.ec
for f in packages/*.ec games/*.ec; do easycrypt compile -I . -I packages -I games $f || break; done
```

> `domino easycrypt` on 4WHS is explicitly allowed — it runs no solver. `domino prove`/`debug` on
> 4WHS remain forbidden.

## 6. Notes / risks

- **`-I` paths**: EasyCrypt resolves `require X` by searching include paths for `X.ec`. Decide and
  document whether generated files sit flat or in `packages/`+`games/` subdirectories *with* the
  `-I` flags the test uses; if subdirectories prove awkward, flattening everything into
  `<out>/<theorem>/` is an acceptable fallback — record which you chose.
- **Don't run the solver.** Export must never invoke cvc5 or touch `EquivalenceContext`.
- **Two theorems, one project**: `Simple4WHS` and `Full4WHS` share packages but get separate
  directories and separate `Types.ec`. That duplication is intended (overview §3).

## 7. State handed to the next story

Record in `05-…-IMPLEMENTATION-REPORT.md`: the CLI surface, `export_theorem`'s signature, the final
directory layout and `-I` convention, the stdout report format, and which example projects export
cleanly today (with the failure reason for any that do not).
