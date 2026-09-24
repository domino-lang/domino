# Story 20 — hello-world and simple-KEM invariants in the `define-state-relation` format

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 06 (invariant translation).
**Blocks:** 23, 24, 26, 27, all of which use hello-world as the second rung of the testing ladder.

---

## 1. Why this story exists

`example-projects/hello-world` is the smallest project on the testing ladder (§7), and it **does
not export**:

```
unsupported SMT sort `<GameState_MediumComposition_<$<!n!>$>>`
```

`simple-KEM-example` fails the same way. Both projects' hand-written invariants use the **old,
solver-facing dialect**: one opaque game-state sort per side, read through selector functions
(`<pkg-state-Rand-<$<!n!>$>-ctr>`, `<game-SmallComposition-<$<!n!>$>-pkgstate-rand>`). Story 06
translates only the flat per-field dialect, `define-state-relation NAME (left right) …`. Story 07's
report (§6.2) documents the gap and pins it with two tests:

- `hello_world_fails_on_its_pre_easycrypt_invariant_format`;
- `simple_kem_example_fails_on_its_pre_easycrypt_invariant_format`

(both in `src/writers/easycrypt/export.rs`).

## 2. Decision

**Migrate the two projects' invariant files to `define-state-relation`.** Don't teach
`invariant.rs` the old dialect. The old dialect is Domino's internal SMT encoding leaking into
project files. Translating it would mean reverse-engineering `src/writers/smt`'s naming scheme,
which story 07 estimated as a story-06-sized job. A migrated file is already proven to work: the
design-session spike exported hello-world with

```
(define-state-relation invariant (left right) (= left.rand.ctr right.rand.ctr))
```

and `example-projects/hello-world-oracle-rename-new/theorem/invariant.smt2` is exactly that file.

## 3. Work to do

1. Rewrite `example-projects/hello-world/theorem/invariant.smt2` in the new dialect, keeping its
   meaning (`ctr` equal on both sides) and its header comment.
2. Rewrite `simple-KEM-example`'s two `invariant-*.smt2` files the same way, relation by relation.
   Mind the `left`/`right` order: the old files take `(state-1 … state-0 …)` in a non-obvious
   order. Check which game is left in the `.ssp` equivalence before translating.
3. **Check that `domino prove` still passes on both projects.** Both are small, so the §7 hard
   rule doesn't apply. The migration must not change a Domino verdict. If `prove` does not accept
   `define-state-relation` for one of them, stop and report it rather than changing the prover.
4. Replace the two failure-pinning tests with export tests: the expected files, and a compile test
   when EasyCrypt is present.

## 4. Acceptance criteria

- [ ] `domino prove` result is unchanged on hello-world and simple-KEM-example (quote before and
      after in the report).
- [ ] `domino easycrypt` exports both. The `Eq_*.ec` files compile, allowing only a base-case
      failure story 19 classified as genuine.
- [ ] `domino inline --easycrypt` on hello-world `UsefulOracle` matches story 08's golden
      (`testdata/easycrypt/story08/inline-hello-world.txt`) byte for byte.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo build --workspace && D=$PWD/target/debug/domino
cd example-projects/hello-world && $D prove && $D easycrypt
cd _build/easycrypt/* && easycrypt compile -I . Eq_*[^s].ec
```

## 6. Notes / risks

- Only project files and tests change. No Rust source under `src/` should need to change. If it
  does, the new dialect has a gap. Describe it and stop.

## 7. State handed to the next story

Record in the report: hello-world and simple-KEM-example export and compile, plus the list of
their equivalences, oracles and the invariant relations each has. Stories 23–27 use hello-world
`UsefulOracle` as their smallest end-to-end case.
