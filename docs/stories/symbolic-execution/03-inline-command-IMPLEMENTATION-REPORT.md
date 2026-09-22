# Story 03 — implementation report (handover)

**Status:** done. Branch `amir/symbolic-execution-debugger`. **Not committed** (commit message at
the bottom).

Read together with `docs/stories/03-inline-command.md`. This was the last unbuilt story of the
epic — stories 05/06/07 shipped ahead of it and `src/debug/render.rs::side_by_side` was already
in the tree as the minimal shared renderer they wrote `inlined.txt` with. Story 03 builds the
full `domino inline` command on top of it **without changing `side_by_side`'s output**, so
`domino debug`'s `inlined.txt` is byte-for-byte unchanged.

`cargo build --workspace`, `cargo test --workspace` (119 passing + 4 ignored lib tests; +5 from
this story — `src/debug/render.rs` had 1 test, now 6), `cargo clippy --workspace` all pass clean.
`domino prove` / `latex` / `proofsteps` / `debug` output is unchanged.

---

## 1. What landed

| File | Change |
|---|---|
| `src/debug/render.rs` | `side_by_side` refactored to delegate to a new `pub fn columns(left, right, line_numbers)` — **`side_by_side(l, r)` is unchanged behaviour** (`= columns(l, r, true)`). New `pub fn render_side_by_side(theorem, proofstep, oracle_name, line_numbers) -> Result<String, RenderError>` and `pub enum RenderError`. +6 tests. |
| `crates/domino/src/cli.rs` | `Inline` subcommand + `Inline` args struct (verbatim from the story). |
| `crates/domino/src/main.rs` | `inline()` dispatch; `pub struct TheoremNotFound(pub String)`; two new local `Error` variants (`TheoremNotFound`, `InlineRender`). |
| `testdata/story03/inline-hello-world.txt` | snapshot fixture for the full-output test (`include_str!`). |

No `Cargo.toml` / `Cargo.lock` change. `inline` needs no solver, so it is **not** behind
`cvc5-lib` (unlike `debug`).

## 2. Public surface

```rust
// src/debug/render.rs
pub fn side_by_side(left: &str, right: &str) -> String;            // unchanged; = columns(.., true)
pub fn columns(left: &str, right: &str, line_numbers: bool) -> String;
pub fn render_side_by_side(
    theorem: &Theorem, proofstep: usize, oracle_name: &str, line_numbers: bool,
) -> Result<String, RenderError>;

pub enum RenderError {
    ProofstepOutOfRange { theorem: String, index: usize, len: usize },
    ProofstepNotEquivalence { theorem: String, index: usize, kind: &'static str },
    Transform(#[from] EquivalenceTransformError),
    Inline(#[from] crate::debug::ir::InlineError),   // covers "oracle not exported", naming the instance
}
```

`theorem` **must be the untransformed theorem** — `render_side_by_side` runs `DebugTransform`
itself (mirrors `run_debug_command`). Theorem lookup stays in `main.rs` (it owns the project), so
"theorem not found" is `main::TheoremNotFound`, not a `RenderError` variant.

`GameHop::Hybrid` is accepted (→ `hyb.equivalence()`), matching `prove`. `Reduction` /
`Conjecture` give `ProofstepNotEquivalence { kind: "reduction" | "conjecture" }`.

## 3. Rendering decisions (these are what story 06/07 already depend on — kept stable)

- **Column separator: `"  |  "`** (two spaces, pipe, two spaces). The left column is padded with
  spaces to the width of its widest line; every row is emitted even when the shorter side has run
  out (trailing `"  |  "` with an empty right cell). This is exactly what `side_by_side` did
  before this story.
- **Line-number gutter: `format!("{:>4} | {}", n, line)`** — 1-based, right-aligned in 4 columns,
  then `" | "`. `--no-line-numbers` (`columns(.., false)`) drops *only* the gutter; padding /
  separator / row count are identical.
- **Left and right are numbered independently.** Printed left line `n` == `Label == n` in the
  left `InlinedOracle::listing.sites` (asserted in
  `hello_world_header_and_left_line_numbers_match_labels`).
- **Header** (2 lines + blank), only in `render_side_by_side`, not in `side_by_side`/`columns`:
  ```
  theorem <T>, proofstep <N> (<Left> == <Right>), oracle <O>
  (left and right line numbers are independent — they index different columns)
  <blank>
  <columns…>
  ```
  `domino inline` prints this with `print!` (no extra trailing newline; `columns` already ends
  every row with `\n`).

## 4. Tests

`src/debug/render.rs` `mod tests` (6):

- `columns_are_numbered_independently_and_aligned` — pre-existing, unchanged.
- `columns_without_line_numbers_drop_the_gutter_only` — `columns(.., false)` vs `true`.
- `hello_world_header_and_left_line_numbers_match_labels` — header prefix + the
  printed-line ↔ `sites` label correspondence (acceptance criterion, asserted not eyeballed).
- `no_line_numbers_flag_removes_the_gutter` — end-to-end through `render_side_by_side`.
- `errors_are_specific` — out-of-range proofstep (reports `len`), reduction proofstep
  (`kind == "reduction"`), unknown oracle (`Inline(OracleNotExported)`).
- `snapshot_hello_world_useful_oracle` — full output pinned against
  `testdata/story03/inline-hello-world.txt`.

Regenerate the fixture (from `example-projects/hello-world`):

```bash
domino inline --proof Proof --proofstep 0 --oracle UsefulOracle > ../../testdata/story03/inline-hello-world.txt
```

Manual smoke (all clean):

```
domino inline --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC   # kem-dem, cross-package invokes
domino inline --proof SplitInvokeProof --proofstep 0 --oracle Query  # test-splitinvoke
domino inline --proof Proof --proofstep 0 --oracle UsefulOracle --no-line-numbers
# errors: unknown theorem / proofstep 5 / proofstep 1 (reduction) / unknown oracle — all miette-rendered
```

## 5. Notes / follow-up

- `main.rs` gained `pub struct TheoremNotFound`. `debug` still uses its own
  `driver::DebugError::TheoremNotFound`; the two are not unified (out of scope).
- `columns` is `pub` (not just `pub(crate)`) for symmetry with `side_by_side`; nothing outside
  the crate uses it yet.
- The kem-dem `PKENC` listing is ~90 lines and wide. As the story predicted, `--no-line-numbers`
  + a pager is the answer; no wrapping/truncation was added (it would break the label ↔ line
  correspondence).
- Epic is now complete: stories 01, 02, 04, 05, 06, 07 committed; 03 in this change.

## 6. Commit message

```
Story 03: `domino inline` — side-by-side inlined-oracle listing

Adds `domino inline --proof <T> --proofstep <N> --oracle <O>
[--no-line-numbers]`: runs DebugTransform, inlines the oracle across
package boundaries for both sides of an equivalence proofstep, and prints
the two labelled listings side by side. The line numbers are exactly the
`L<n>` labels `domino debug` reports.

`src/debug/render.rs`: `side_by_side` is refactored onto a new
`columns(left, right, line_numbers)` with byte-identical output, so the
`inlined.txt` `domino debug` writes is unchanged. New `render_side_by_side`
does the transform + inline + header; `RenderError` covers out-of-range /
non-equivalence proofsteps and wraps `InlineError` (unknown oracle names
the game instance). Hybrids are accepted as their equivalence, matching
`prove`.

Snapshot-pinned against testdata/story03/inline-hello-world.txt; a test
asserts printed left line n == listing site label n.

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01BrBZJz8hq9fqSkecgKfM6H
```
