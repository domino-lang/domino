# Story 26 — implementation report

## What changed

- New module `src/easycrypt/` (`pub mod easycrypt` in `lib.rs`):
  - `json.rs`: the Rust mirror of `domino-json/1`, lenient (unknown fields ignored). `Form` is one
    struct with the union of the fields read (`kind`, `pp`, `op`, `head`, `args`, `quantifier`,
    `binders`, `body`, `left`/`right` as `Side`, `pre`, `post`), not an enum; `Instr` for programs.
  - `session.rs`: `Session` (spawn, capability check, send, undo, interrupt, transcript) and
    `split_sentences`.
  - `skeleton.rs`, `align.rs`: decision skeletons and alignment.
  - `check.rs`: `check_alignment`, `align_goal`, the report.
- `domino easycrypt --check-alignment [--proofstep N] [--oracle O]` (`crates/domino`): exports as
  usual, then aligns; prints the report, writes `<out>/<theorem>/alignment.txt`, exits non-zero
  (`AlignmentMismatch`) on any mismatch or unreachable goal. Without the flag nothing changed:
  the exports of hello-world, simple-KEM, kem-dem and 4WHS were diffed byte for byte against the
  pre-change binary.
- `EquivalenceReport.proofstep` / `EquivalenceProofFile.proofstep` (the hop's index in
  `theorem.game_hops`), and `router_module_and_flag` is now `pub(crate)`.
- Fixture `testdata/easycrypt/story25/hello_world_useful_oracle_after_inline.json`: the answer to
  `proc; inline.` on hello-world's `UsefulOracle`, recorded with story 25's binary.

## The API story 27 consumes

```rust
// session
Session::start(dir: &Path) -> Result<Session, SessionError>;      // DOMINO_EASYCRYPT, else `easycrypt`
Session::start_with(binary: &Path, dir: &Path) -> Result<Session, SessionError>;
session.send(&str) -> Result<&Response, SessionError>;            // one sentence
session.undo_to(state: u64) -> Result<&Response, SessionError>;   // `undo N.`
session.interrupt();  session.set_timeout(Duration);              // default 600 s, then SIGINT
session.last() -> Option<&Response>;  session.goals() -> &[Goal];
session.transcript() -> &[Exchange];                              // sentence + Response, in order
split_sentences(&str) -> Vec<String>;                             // sentence splitter (comments dropped)
json_binary_configured() -> bool;                                 // for tests that skip
// json
Response { version, state, status: Status::{Ok,Error,Interrupted}, error, messages, proof }
Goal { id, tvars, hyps: Vec<Hyp>, concl: Form, text }
Form::equiv_procs() -> Option<(&Proc, &Proc)>                     // an equivF's two procedures
// skeleton / alignment
ec_skeleton(&[Instr]) -> Skeleton;  ir_skeleton(&InlinedOracle) -> Skeleton;
align(ec, ir) -> Alignment;  align_router(ec, ir, abort_flag) -> Alignment;
Alignment { matches: Vec<DecisionMatch>, mismatches: Vec<Mismatch> }; alignment.ec_for(label)
DecisionMatch { ir_label, kind: Branch|Sampling|End, plumbing, ec: EcInstr { pos: Option<EcPos>, pp, lvalue } }
EcPos { path: Vec<(usize, Arm)>, index: usize }     // counts every statement, assignments included
// check
align_goal(goal, (&left_ir, left_flag), (&right_ir, right_flag)) -> Option<[SideAlignment; 2]>
check_alignment(theorem, &exported, out_dir, &CheckOptions) -> Result<TheoremAlignment, CheckError>
```

`abort_flag` is `<Router module>.abort_flag` as `router_module_and_flag` names it
(`Game_<Comp>.abort_flag`); the guard's `pp` must contain it. The goal to compare is chosen from
the JSON: the first goal, whose `equivF` procedure name is matched against the mangled export
names (`Names::mangle(NameKind::Proc, …)`); the base case is the `equivS` goal.

## Skeletons, alignment, mismatch kinds

- EasyCrypt side: `asgn` skipped; `if` a branch (both blocks); `rnd` a sampling carrying the
  lvalue `pp` and an `EcPos`; anything else `Unknown`. EasyCrypt's own end is implicit (no end
  node): the IR end swallows what is left of the block. (Deviation from §3.2's "the end becomes an
  end node".)
- IR side: `Branch` (carries `plumbing`), `Sample`, `Unwrap` (as a branch whose else is an end),
  `Call` frames spliced in transparently (a callee's `Return` and closing `Abort` leave nothing),
  an entry-frame `Return`/`Abort` is an end.
- `align`: equal kinds match and branches recurse; an IR end matches the rest of the EasyCrypt
  block; on disagreement it resynchronises: first a pure insertion/deletion after which the rest
  agrees exactly, otherwise the next pair that agrees exactly, otherwise a one-for-one
  substitution. Kinds: `kind-differs`, `extra-ec-decision`, `missing-ec-decision`,
  `unknown-ec-instruction`, `router-shape`. Each mismatch has the path (IR label and arm of each
  enclosing branch), EasyCrypt's `pp` and position, and the IR node.
- `align_router` peels the router: the program must be exactly one `if` without else whose
  condition contains the router's abort flag.

## Results: alignment on the testing ladder (`--check-alignment`, debug build, ec.native)

| project | equivalences | oracles | mismatches | time |
|---|---|---|---|---|
| hello-world | 1 | 1 | 0 | 1.2 s |
| simple-KEM-example | 2 | 8 | 0 | 3.5 s |
| kem-dem-cca-ssp | 1 | 3 | 0 | 1.9 s |
| Simple4WHS | 3 | 27 | 0 | 14.5 s |
| Full4WHS | 9 | 108 | 0 | 86.6 s |

**147 oracles, zero mismatches, no lowering fix needed.** Both sides of every oracle were
compared (294 program alignments). The checks are not vacuous: PKENC aligns 37 decisions, and
`the_recorded_goal_aligns_with_the_lowering_without_easycrypt` shows a removed IR sampling and a
wrong router name each produce a mismatch.

## EasyCrypt behaviour alignment had to accept

Nothing beyond what §8.1b already said; the additions recorded there (router tail inside the
guard, call frames transparent, only `asgn`/`rnd`/`if` seen) are observations, not exceptions.
`pr` formulas carry `args` as a single formula (the mirror accepts either).

## Deviations

- Module is `src/easycrypt/` (as suggested), the CLI flag for the project is the existing
  `--project` of `domino easycrypt`.
- No explicit EasyCrypt end node (above).
- The capability probe is `pragma Goals:printall.`: answered with one line, pushes no undo level.
- `Session::interrupt` shells out to `kill -INT` (no `libc` dependency). Each equivalence gets its
  own session (a fresh EasyCrypt process, about 1.5 s to reach the oracle goals in 4WHS).
- `assert` is no longer a keyword in the newer EasyCrypt: nothing in the exporter emits it (grep
  of `src/writers/easycrypt` finds none), and all exports load in `ec.native`.

## Open issues / notes for 27

- `Full4WHS` takes 87 s, of which most is EasyCrypt loading and the 100-350 KB JSON lines being
  parsed in a debug build; story 27 will run per oracle, not per file.
- `EcPos` counts every statement in EasyCrypt's list but is only as stable as EasyCrypt's inliner;
  story 27 should use `^if` patterns where it can (ADR 0002).
- `Session` keeps the transcript in memory but drops the goals (`proof`) of every answer except
  the newest, since a goal is 100-350 KB of JSON. Peak RSS of `--check-alignment` on one Full4WHS
  equivalence is 727 MB against 692 MB for the plain export of the same theorem (debug build):
  the export dominates, alignment adds about 35 MB.

## Verification and code review

- `cargo build/clippy --workspace --all-targets`: clean. `cargo test --workspace` (with
  `DOMINO_EASYCRYPT` set): 447 lib tests pass. With `--features cvc5-lib`: 504 pass, 1 fails, the
  failure that predates story 23 (`goal_smt_is_empty_for_an_admitted_claim`).
- Two parallel reviews (standards, spec). Fixed: unused `mismatch_kinds` removed; the proofstep
  index is passed into `build_equivalence_file` instead of patched in afterwards; the goal is
  matched on the router modules as well as the procedure name; the spawn error no longer reads as
  if `ec.native` were required for a `PATH` `easycrypt`. Left on purpose: the tuple-passing and
  duplicated left/right setup in `check.rs`; the implicit EasyCrypt end (deviation above); a
  resync that pairs structurally identical branches may pick the wrong twin (only ever after a
  mismatch has already been reported). The suspected "End consumed by resync" does not occur:
  an end never agrees strictly, and it is always last in an IR list, so it is never skipped.
