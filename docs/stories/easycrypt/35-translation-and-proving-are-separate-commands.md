# Story 35 — Translation and proving are separate commands

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 32 (the overwrite check), 33, 34.
**Blocks:** 36, 37.
**Records:** `docs/adr/0006-a-proof-job-never-translates.md`.

---

## 1. Why this story exists

The owner: *"I can not parallelize proof translation to EasyCrypt for several gamehops/proofsteps
… as the first step we translate and it tries to rewrite the translation while translation should
be a separate step and proof translation should be another process! Ideally proof translation
should only focus on one equivalence file … It should only make sure that packages are translated
and relevant files are there. Otherwise it could try to generate them! If a file with expected
name is there, it does not need to care about the content and can proceed directly to the proof."*

Today `domino easycrypt --tactics --proofstep N` builds the whole export in memory, writes the
whole tree (`write_all_observed` in `crates/domino/src/main.rs`), then proves. Since story 32 the
write refuses to happen without `--force` once the tree exists, and `--force` rewrites every other
equivalence's `Eq_*.ec`. So a second proofstep can only be started by destroying the first one's
proof.

Vocabulary (`CONTEXT.md`): **translation**, **proof job**, **tactics run**, **session record**.

## 2. Inherited from earlier stories

- **Story 32 / ADR 0004:** `check_export_tree` (`src/writers/easycrypt/overwrite.rs`), the run
  artifact exemptions (`RUN_ARTIFACT_DIRS`, `*.report.txt`, `alignment.txt`).
- **Stories 33, 34:** incremental writes of `Eq_*.ec` through `ProofFile::write`, the seal, Ctrl-C.
- **Symbolic-execution story 19:** `domino easycrypt --debug` (lockstep execution on the
  EasyCrypt listing) exists as a third mode beside `--check-alignment` and `--tactics`, in the clap
  group `ec_mode` (`crates/domino/src/cli.rs`).

## 3. Work to do

### 3.1 The command shape

```
domino easycrypt [--theorem T] [--out DIR] [--force] [--progress …]      # translation only
domino easycrypt prove --theorem T [--proofstep N] [--oracle O] [--force|-f]
                       [--ec-timeout …] [--leaf-budget …] [--no-rung0]
                       [--ec-transcript …] [--write-granularity …] [--progress …]
domino easycrypt check-alignment --theorem T [--proofstep N] [--oracle O]
domino easycrypt debug --theorem T [--proofstep N] [--oracle O] [--debug-timeout …]
```

- `--tactics`, `--check-alignment` and `--debug` are **removed** from the plain command, not
  aliased. Plain `domino easycrypt` does exactly what it did without them, ADR 0004 check included.
- `prove`: `--theorem` is required. Without `--proofstep` it runs the proofsteps one after another
  in one process. Parallelism comes from starting several processes (story 36), not from threads.
- `check-alignment` and `debug` move to subcommands for the same reason `prove` does: they talk to
  EasyCrypt or the solver, never translate, and follow §3.2's rules. They keep their current
  outputs.
- `--project` and `--out` are accepted by every subcommand with today's meaning.

### 3.2 What a proof job may assume and touch

The job's inputs, split by who owns them:

| File | Owner | If present | If missing |
|---|---|---|---|
| everything translation writes except `Eq_*.ec` (types, package variants, games, invariants, `Domino_` operators) | translation | used as is, contents never read | created, §3.3 |
| `Eq_<L>_<R>.ec` of **this** equivalence | the job | rewritten by the tactics run | created from the skeleton |
| `Eq_*.ec` of any **other** equivalence | another job | never touched | not created |
| `Eq_<L>_<R>.session.json` of this equivalence | the job | §3.4 | the job proves from scratch |

A proof job still needs translation's result **in memory** (`ExportedTheorem`, the equivalence
setup, the skeleton) — it computes it, it just does not write it over what is there. Restricting
the in-memory translation to what one equivalence needs is allowed but not required; measure it on
kem-dem and record it.

`--force` on `prove` concerns only this equivalence: it discards the session record and restarts
the proof from the skeleton. It never rewrites a translation file. A stale translation file is
fixed by `domino easycrypt --force`.

### 3.3 Creating a missing file

Write to a temporary file in the same directory, then `std::fs::hard_link` it to the target name
(which fails if the target already exists), then remove the temporary. If the link fails because
another job created the file first, that is success: the file is there. Never `rename` (it
replaces) and never write the target in place (a concurrent job could load a half-written file).

Print one line per created file on stderr, e.g. `created Types.ec (missing from the translation)`,
so the user sees that the job did translation work.

### 3.4 The session record, minimal form

This story introduces `Eq_<L>_<R>.session.json` with only what skip/force needs. Story 37 adds
resume and the per-node content.

```json
{"version": 1, "theorem": "…", "left": "…", "right": "…", "complete": true,
 "oracles": [{"name": "PKENC", "status": "done"}, {"name": "DEC", "status": "interrupted"}]}
```

- Written at the same checkpoints as `Eq_*.ec` and **after** it, atomically. Proof file first:
  a crash between the two leaves a record that claims less than the file holds, which costs a
  re-proof. The other order would claim a proof the file does not hold.
- `status` is `done` if the oracle ended without an `interrupted` admit (admits with any other
  reason count as done), `interrupted` if it was sealed, `pending` if not reached.
- **Record present** (complete or not): warn and skip the equivalence, exit 0:
  `skipping Eq_L_R: already proved (3 of 3 oracles); --force re-proves it`. A partial record says
  `k of n` and adds `resuming arrives with story 37`.
- **No record:** prove, overwriting the skeleton.

### 3.5 Translation and the session record

- ADR 0004's check treats `*.session.json` like any translation output: its presence makes plain
  `domino easycrypt` refuse without `--force`.
- `domino easycrypt --force` deletes every `*.session.json` under the theorem's directory, since
  the proofs they describe are overwritten by the skeletons. Translation does not otherwise write
  session records.

### 3.6 Lockstep output follows `--out`

`tactics_for_oracle` calls `run_lockstep_command(…, None, …)`, and `None` makes
`src/debug/lockstep_run.rs` put the output under `<project>/_build/easycrypt/<theorem>/!debug!/`
whatever `--out` says. Pass the path rooted at the job's `<out>/<theorem>/!debug!/` instead, in
`prove` and `debug` alike.

## 4. Acceptance criteria

- [ ] `domino easycrypt` on kem-dem writes the tree and runs no EasyCrypt; `--tactics`,
      `--check-alignment` and `--debug` are rejected by clap as unknown.
- [ ] After translation, `domino easycrypt prove --theorem T --proofstep 0` proves without `--force`
      and without modifying any file but its own `Eq_*.ec`, its report, its session record and run
      artifacts. Check with mtimes/hashes of every other file before and after.
- [ ] With `Types.ec` (or any translation file) deleted, `prove` recreates it, prints the
      `created …` line, and proves. With it replaced by garbage, `prove` does not look at it and
      the EasyCrypt error that follows is reported as usual.
- [ ] A second `prove` on the same proofstep prints the skip line and exits 0; with `-f` it
      re-proves.
- [ ] `prove` never creates another equivalence's `Eq_*.ec`.
- [ ] The create-if-absent helper has a unit test: two threads creating the same file both succeed
      and the file holds one complete copy.
- [ ] `domino easycrypt` without `--force` refuses when a `*.session.json` exists; with `--force`
      the records are gone afterwards.
- [ ] `prove --out /tmp/x` puts `!debug!/` under `/tmp/x/<theorem>/`.
- [ ] `check-alignment` and `debug` produce the same outputs as the old flags on kem-dem.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh; export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --force
$D easycrypt prove --theorem <T> --proofstep 0
$D easycrypt prove --theorem <T> --proofstep 0      # skipping …
rm _build/easycrypt/<T>/Types.ec && $D easycrypt prove --theorem <T> --proofstep 0 -f
```

## 6. Notes / risks

- The old flags disappear outright, so scripts, tests and docs that call `--tactics`,
  `--check-alignment` or `--debug` break. Update them in the same change: `grep -rn -- '--tactics'`
  across `docs/`, `scripts/`, `src/`, `crates/` and the skill files.
- Proving against a translation that is out of date is now silent. This is deliberate, see
  ADR 0006's consequences.
- 4WHS and yao stay off-limits for `prove` and `debug` (overview §7).

## 7. State handed to the next story

Record in the report: the cost of the in-memory translation per `prove` on kem-dem, and every place
that still assumes one tactics run per theorem (the transcript file, the live page, the temporary
directory used for atomic writes). Story 36 moves those.
