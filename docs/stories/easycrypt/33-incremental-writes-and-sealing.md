# Story 33 — The file on disk is what is proven: incremental writes and sealing

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Records:** `docs/adr/0005-no-easycrypt-compile-in-a-tactics-run.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 27 (`--tactics`, the script and the report), 28 (the live page), 31 (the bounded
transcript — without it a development loop on kem-dem is not affordable), 32 (or the files this
story produces get clobbered by the next export).
**Blocks:** 34 (whose deliverable *is* the seal).

---

## 1. Why this story exists

The owner: *"we don't get intermediary EasyCrypt proof of oracles if I stop the interactive
translation mid equivalence hop"*, and the property to establish: *"Let the file written to disc be
what is proven so far."*

Today `tactics_for_equivalence` writes `Eq_*.ec` **once**, after the whole oracle loop has finished
and the session has been dropped, and `Eq_*.report.txt` right after. So a tactics run is
all-or-nothing per equivalence: earlier equivalences are on disk, the one in flight is lost
entirely. On kem-dem that is up to twelve minutes and three proved oracles thrown away because you
stopped during the fourth.

This story makes the proof files hold what has been proved so far, at all times, under every way a
run can end — Ctrl-C (story 34), a crash, a full disk, EasyCrypt dying.

## 2. Inherited from earlier stories

- **Story 27:** `tactics_for_equivalence` and `tactics_for_oracle` in
  `src/easycrypt/tactics/mod.rs`; the file rewrite as a text replacement of the line after
  `(* <proc> *)`, replacing `+ proc; inline. admit.`; the `easycrypt compile` gate and its
  revert-on-failure path; `Eq_*.report.txt`; `AdmitReason` with `ALL` and `slug()`
  (`src/easycrypt/tactics/driver.rs`) and the admit label format.
- **Story 27:** `Script` (`src/easycrypt/tactics/script.rs`) — accepted sentences only, `depth`,
  `pending_bullet`, `enter_bullet`/`leave_bullet`, `mark`/`rollback`, and `render` rebuilding
  bullets and indentation from the depth.
- **Story 28:** `LiveHandle::oracle_finished` / `equivalence_finished` / `activity`, the goal model,
  and the page's admit rows.
- **Story 31:** `ec-transcript.jsonl` is capped by default (at most 3 goals of 12 000 characters
  per record; `src/easycrypt/transcript.rs`), ~250 kB for kem-dem `--oracle PKGEN` against 4.06 MB
  in full; `--ec-transcript full` restores verbatim answers. Under `capped` a failed transcript
  write (a full disk) no longer fails the run: `Session` drops the sink with one stderr warning and
  `SessionEvent::TranscriptDropped`, and `run_tactics` stops giving later sessions the file. Under
  `full` it fails with `SessionError::Transcript` naming the path.
- `Prover` already knows the open-goal count (`self.session.goals().len()`,
  `src/easycrypt/tactics/driver.rs`).

## 3. Work to do

### 3.1 Seal

**Seal** an oracle = close every goal it still has open with `admit`, so its bullet is a complete
proof even though the walk had not finished it (`CONTEXT.md`, *seal*).

Sealing is a **pure `Script` operation. Nothing is sent to EasyCrypt.** `Script` already tracks
`depth` and `pending_bullet`, and `session.goals().len()` already gives the count, so the seal
closes the current bullet and emits `+ admit.` per remaining goal locally. Sending the admits would
cost a sentence each plus an `undo` per seal, every one of them logged to the transcript and making
EasyCrypt print every open goal — on a 43-node oracle in per-node mode, ~90 expensive sentences to
protect a proof that cost less.

Each sealed admit is labelled with the story-27 format under a new `AdmitReason::Interrupted`, slug
`interrupted`, which the report's by-reason table picks up for free.

A seal is not destructive: the `Script` is sealed into a *copy* for writing, and the walk continues
from the unsealed one.

### 3.2 `--write-granularity <oracle|node>`

Default `oracle`.

- `oracle`: write after each oracle finishes (`LiveHandle::oracle_finished` is the existing hook).
  Nothing is open at that point, so the seal is a no-op.
- `node`: seal and write after every joint node. For the case you are sitting on a `PKENC` that
  takes 691 s and want to watch the proof accumulate.

A value enum, matching `--progress` and `--smt` which this CLI already uses, so a third setting
later needs no second flag.

The two granularities are **one mechanism**: "seal, write, continue". Per-oracle is that mechanism
called at oracle boundaries.

### 3.3 The report follows the file

`Eq_*.report.txt` is rewritten with every write of the `.ec`. It is a few kB of text against
sentences costing seconds, and a `.ec` full of proved bullets next to a report describing an earlier
state is worse than no report at all.

### 3.4 Remove `easycrypt compile` from the run

See ADR 0005. The gate goes; `compile` stays, called only by the two tests in
`src/easycrypt/tactics/tests.rs` that already use it. `OracleTactics::reverted` and the report's
`BUG:` line go with it.

The owner: *"Let's not run easycrypt compile. When we generate proofs we are constantly
communicating with EasyCrypt so it can't be that entire proof does not go through when we stop."*
The decisive reason is the second one in the ADR: the gate's recovery path rewrites the file with
**fewer proofs than were proved**, which is precisely what this story exists to prevent. A mechanism
whose failure mode is discarding proved work cannot sit in a pipeline whose point is never to
discard proved work.

This is also what makes `node` granularity affordable: writes become a file write, not a compile.

### 3.5 Oracles not yet reached

Keep `+ proc; inline. admit.`, unlabelled, exactly as story 27 leaves an oracle that was not asked
for. The distinction the report already draws — labelled admits are the walk's, unlabelled ones are
untouched bullets — must survive.

## 4. Acceptance criteria

- [ ] `--write-granularity oracle` (the default): after each oracle, `Eq_*.ec` on disk contains
      that oracle's script. Assert by reading the file *during* a run, between oracles.
- [ ] `--write-granularity node`: the file is a complete, sealed proof after every node. Capture it
      at N points during a hello-world run and assert every capture is a full bullet structure whose
      admits are all labelled.
- [ ] A sealed file compiles: `easycrypt compile` accepts a file captured mid-oracle. (Run by the
      test, not by the tool — §3.4.)
- [ ] Sealing sends nothing: the transcript of a `node`-granularity run holds no `admit.` sentence
      that the walk did not itself decide on, and no `undo` attributable to a seal.
- [ ] The report next to a mid-run `.ec` describes that `.ec`: admit counts agree, including the
      `interrupted` ones.
- [ ] Killing the process (`SIGKILL`) mid-oracle leaves the last written state intact and readable.
- [ ] `AdmitReason::Interrupted` appears in `ALL` and in the by-reason table; story 27's test that
      the report's admit count equals the file's labelled admits still holds.
- [ ] Two runs on an unchanged project still write the same `Eq_*.ec` (story 27's determinism test).
- [ ] No `easycrypt compile` runs during a tactics run (assert by counting process spawns, or by
      running with a binary that fails on `compile`).
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh; export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --tactics --proofstep 0 --write-granularity node &
while sleep 5; do cp _build/easycrypt/*/Eq_*.ec /tmp/snap-$(date +%s).ec; done
# every snapshot must be a complete proof; check a few with `easycrypt compile`
```

## 6. Notes / risks

- **4WHS and yao stay off-limits for `--tactics`** (overview §7): it runs lockstep execution.
- Per-node writing on a long oracle means many file writes. They are cheap now that §3.4 removed the
  compile, but write the file atomically (temp + rename, as the live page already does) so a reader
  never sees a half-written proof.
- An interrupted per-node file is *probably* compilable rather than certainly so — that is the
  accepted consequence of §3.4, and the acceptance criteria check it on real runs instead.
- Story 27's `--leaf-budget` already makes which part of a leaf is cut depend on timing. Per-node
  writes do not make that worse, but a mid-leaf capture is not reproducible; test determinism at
  oracle boundaries.

## 7. State handed to the next story

Story 34 needs: the seal entry point, the granularity plumbing, and `AdmitReason::Interrupted`.
Record where a seal can be requested from, because Ctrl-C will request one from a signal-driven
stop check rather than from the write loop.
