# Story 20 — implementation report

Only project files and tests changed; no Rust under `src/` outside test modules. The new dialect
had no gap.

## Migrated files

- `example-projects/hello-world/theorem/invariant.smt2` -> `(define-state-relation invariant (left right) (= left.rand.ctr right.rand.ctr))`, header comment kept.
- `example-projects/simple-KEM-example/theorem/invariant-KEM_Proof-Prot_Real-H1_Real.smt2` (left `Prot`, right `H1`) and `invariant-KEM_Proof-H1_kem_correctness_ideal-H2.smt2` (left `H1`, right `H2`), relation by relation. The `randomness-mapping-*` `define-fun`s were left as they were (the prover needs them; the exporter notes them as skipped).

## `domino prove` before and after

`domino prove` prints nothing on success and exits 0; a failure prints `error proving claim ...`.
Before (old files, HEAD~1) and after (migrated), in each project directory:
`$ domino prove; echo $?` prints `0` and nothing else, for hello-world and simple-KEM-example alike.
With one relation deliberately broken, hello-world prints
`oracle UsefulOracle: error proving claim same-output. status: sat.` and simple-KEM-example prints
`error proving claim ...`, so the silence really is a pass. Sanity check that the prover
does check the migrated files: breaking one relation makes both projects fail.

## Verification

`cargo build/test/clippy --workspace`: clean (421 lib tests pass, 5 ignored, as before).

- `domino easycrypt` exports both; every `Eq_*.ec` and `Eq_*_Invariants.ec` compiles under
  `easycrypt compile -I .` with no base-case failure.
- `domino inline --easycrypt` on hello-world `UsefulOracle` is byte-identical to
  `testdata/easycrypt/story08/inline-hello-world.txt`.
- `export.rs`: the two failure-pinning tests are replaced by `hello_world_exports_its_one_equivalence`,
  `simple_kem_example_exports_its_two_equivalences` and two `*_full_tree_compiles` tests (shared
  helper `assert_tree_compiles`; skip without `easycrypt`).

## State handed to the next story

Instance names in invariants are the *package instance* names inside each composition.

hello-world (`Proof`): one equivalence `medium_composition ~ small_composition`, oracle
`UsefulOracle`; relation `invariant`: `ctr` of package instance `rand` equal. Export report: 1
oracle, 1 admit. Also has a skipped reduction hop and one `randomness: simple` oracle.

simple-KEM-example (`KEM_Proof`), both with oracles `GetPK`, `Run`, `TestSender`, `TestReceiver`
(4 admits each), one relation `invariant` each:
- `Prot ~ H1_kem_correctness_real`: every `Prot` state field (`SENTCTXT`, `SENTKEY`, `RECEIVEDCTXT`,
  `RECEIVEDKEY`, `TESTED`, `ctr`, `sk`, `pk`) equals its counterpart in `H1.Corr_reduction` /
  `H1.Corr_KEM`.
- `H1_kem_correctness_ideal ~ H2`: `Corr_reduction` SENT/RECEIVED CTXT/KEY equal, and equal to
  `CPA.CTXT`/`CPA.KEY`; `TESTED`, `ctr` equal `CPA`'s; `Corr_KEM.sk`/`pk` equal `CPA.sk`/`pk`.
- Two reduction hops are skipped in the export.
