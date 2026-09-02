# Story 03 — `domino inline` command

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 02 (`DebugTransform`, `src/debug/ir.rs`, `inline_oracle`).
**Blocks:** nothing (but it is the fastest way to eyeball story 02's output, and story 06 reuses
the same listing).

---

## 1. Why this story exists

The debugger reports execution paths as **line numbers into the inlined listing**
(`L12:then`, `L19:assert-holds`, `L27:return`). Those numbers are useless unless the user can
print the listing. `domino inline` is that command: it prints the left and the right game
instance's inlined oracle side by side, with line numbers, for one equivalence proofstep.

It also gives story 02's IR a user-visible surface, so the IR can be reviewed and merged before
the executor exists.

There is prior art: branch `amir/ty-params-features` (and `amir/code-inlining`) carries
`src/inline.rs`, a ~740-line textual inliner with a `domino inline --proof --proofstep --oracle`
command. **Do not port it wholesale** — story 02 replaced its inlining logic with the IR. Port
only its *presentation* (the `side_by_side` helper and the error taxonomy) and render from
`InlinedOracle::listing`.

## 2. Inherited from earlier stories

From story 02:

- `crate::transforms::theorem_transforms::DebugTransform`, a `TheoremTransform` with
  `Aux = Vec<(String, GameInstAux)>`, running the pipeline **without `treeify`**.
- `crate::debug::ir::{InlinedOracle, Listing, SiteInfo, SiteKind, Label, inline_oracle,
  InlineError}`.
- `InlinedOracle::listing.text` is the rendered code (no line numbers baked in) and
  `listing.sites: BTreeMap<Label, SiteInfo>` maps 1-based line numbers to the labelled sites.
- The listing is deterministic for an unchanged project.

## 3. What exists today

`crates/domino/src/cli.rs` — `Commands` is a `clap` `Subcommand` enum with `Latex`, `Prove`,
`Format`, `Proofsteps`. Each variant has an args struct; `Prove` and `Latex` and `Proofsteps`
each carry:

```rust
/// Path to the Domino project. Defaults to searching the current
/// directory and its ancestors for an `ssp.toml`.
#[clap(long)]
pub(crate) path: Option<std::path::PathBuf>,
```

`crates/domino/src/main.rs` — `fn main` matches on `cli.command` and dispatches to
`prove(p) | proofsteps(p) | latex(l) | format(f)`. The project-loading preamble is the same
three lines everywhere:

```rust
let project_root = p.path.to_owned().unwrap_or(project::directory::find_project_root()?);
let files   = project::DirectoryFiles::load(&project_root)?;
let project = project::DirectoryProject::load(project_root, &files)?;
```

`src/project/mod.rs` — the `Project` trait; `get_theorem(name) -> Option<&Theorem>`;
`theorems() -> impl Iterator<Item = &str>`; `proofsteps()` prints the numbered proofstep list.

`src/theorem.rs` — `Theorem { name, consts, instances, assumptions, proofs, game_hops, pkgs }`;
`Theorem::find_game_instance(name) -> Option<&GameInstance>`.

`src/gamehops/mod.rs` — `GameHop::{Equivalence(Equivalence), Reduction, Conjecture, Hybrid}`.
`Equivalence::{left_name(), right_name(), theorem_name(), trees()}` are in
`src/gamehops/equivalence/mod.rs`.

The reference implementation to crib presentation from:

```bash
git show amir/ty-params-features:src/inline.rs
```

Its `side_by_side(left: &str, right: &str) -> String` pads the left column to the width of its
longest line and joins with ` | `.

## 4. Work to do

### 4.1 CLI

Add to `crates/domino/src/cli.rs`:

```rust
/// Inline the code of an oracle for both sides of an equivalence proofstep, side by side.
Inline(Inline),

#[derive(clap::Args, Debug)]
#[clap(author, version, about, long_about = None)]
pub(crate) struct Inline {
    /// Path to the Domino project. Defaults to searching the current
    /// directory and its ancestors for an `ssp.toml`.
    #[clap(long)]
    pub(crate) path: Option<std::path::PathBuf>,
    /// Name of the theorem the equivalence proofstep belongs to.
    #[clap(long)]
    pub(crate) proof: String,
    /// Index (starting at 0) of the equivalence proofstep within the theorem,
    /// as printed by `domino proofsteps`.
    #[clap(long)]
    pub(crate) proofstep: usize,
    /// Name of the oracle to inline, as exported by the games in the proofstep.
    #[clap(long)]
    pub(crate) oracle: String,
    /// Print without line numbers (useful for diffing two runs).
    #[clap(long)]
    pub(crate) no_line_numbers: bool,
}
```

Dispatch it in `crates/domino/src/main.rs` alongside the others.

### 4.2 Renderer — `src/debug/render.rs`

```rust
pub fn render_side_by_side(
    theorem: &Theorem,
    proofstep: usize,
    oracle_name: &str,
    line_numbers: bool,
) -> Result<String, RenderError>;
```

Steps:

1. Look up `theorem.game_hops[proofstep]`; require `GameHop::Equivalence(eq)` (accept
   `GameHop::Hybrid(h)` too by using `h.equivalence()`, matching what `prove` does in
   `src/project/mod.rs:169`).
2. Run `DebugTransform.transform_theorem(theorem)` and take the transformed instances.
3. `inline_oracle(left_inst, oracle_name)` and `inline_oracle(right_inst, oracle_name)`.
4. Prefix each listing line with its 1-based number (unless `--no-line-numbers`), then
   `side_by_side`.
5. Header line: `theorem <T>, proofstep <N> (<Left> == <Right>), oracle <O>`.

Errors (`RenderError`), mirroring `amir/ty-params-features:src/inline.rs`:

- theorem not found
- proofstep index out of range (report how many exist)
- proofstep is a reduction/conjecture (say which, and that `inline` only supports equivalences)
- oracle not exported by a game instance (name the instance)
- anything `InlineError` reports, wrapped transparently

Use `thiserror` + `miette::Diagnostic` like the rest of the codebase, and add the variant to
`crates/domino/src/main.rs`'s local `Error` enum.

### 4.3 Output shape

```
theorem kem_dem_cca_ssp, proofstep 0 (Game_MON_CCA_PKE == Game_MOD_CCA_PKE_Real_KEM), oracle PKENC

  1 | // game instance: Game_MON_CCA_PKE  ...     |   1 | // game instance: Game_MOD_CCA_PKE_Real_KEM ...
  2 | PKENC(m: Bits(ptl)) -> Bits(dctl) {         |   2 | PKENC(m: Bits(ptl)) -> Bits(dctl) {
  3 |     assert (pk != bot);                     |   3 |     assert (pk != bot);
  ...
```

The two sides are numbered **independently** — a path label `L12` on the left refers to the left
column's line 12. Make that explicit in the header or a footnote, because it is the single
easiest thing to misread.

## 5. Acceptance criteria

- [ ] `domino inline --proof <T> --proofstep <N> --oracle <O>` prints both sides side by side
      with independent 1-based line numbers.
- [ ] Line `n` of the printed left column corresponds to `Label == n` in the left
      `InlinedOracle::listing.sites` (assert this in a test, don't just eyeball it).
- [ ] `--no-line-numbers` prints the same content without the numeric gutter.
- [ ] Clear, `miette`-rendered errors for: unknown theorem; out-of-range proofstep; proofstep is
      a reduction; oracle not exported.
- [ ] Snapshot test pinning the full output for one small project
      (`example-projects/hello-world` or `test-projects/test-splitinvoke`).
- [ ] `cargo build --workspace && cargo test --workspace` pass.

## 6. How to verify

```bash
cargo build --workspace
cargo test  --workspace

cd example-projects/hello-world
cargo run --bin domino -- proofsteps
cargo run --bin domino -- inline --proof <theorem-name> --proofstep 0 --oracle <O>

cd ../../example-projects/kem-dem/kem-dem-cca-ssp
cargo run --bin domino -- proofsteps
cargo run --bin domino -- inline --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC
cargo run --bin domino -- inline --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC
```

`kem-dem-cca-ssp` proofstep 0 is `equivalence Game_MON_CCA_PKE Game_MOD_CCA_PKE_Real_KEM`
(`theorem/Proof.ssp:237`) with oracles `PKGEN`, `PKENC`, `PKDEC`. It is the primary target for
this epic: real branching, sampling and cross-package invokes, and it renders in a moment.

> **Never** run against `example-projects/4WHS` or `example-projects/yao` — the two slow projects
> in `example-projects/known-good-slow.txt`. `inline` itself would be fast, but do not get in the
> habit; see `docs/stories/00-overview.md` §7.

## 7. Notes / risks

- Terminal width: kem-dem lines can be long. Do not wrap or truncate — a wrapped line would break
  the line-number ↔ label correspondence. If it is unreadable, that is what `--no-line-numbers`
  plus a pager is for.
- Keep the renderer free of solver or SMT concerns. It reads the IR and prints; nothing else.

## 8. State handed to the next story

Story 06 will rely on:

- `crate::debug::render::render_side_by_side(...)` — it writes the same listing to
  `_build/debug/.../inlined.txt` so the labels in the debug tree can be looked up.
- The convention that left and right line numbers are independent.

Record here any rendering decision you made that story 06 or 07 must match (column separator,
header format, how you numbered blank/structural lines).
