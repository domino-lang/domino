# Story — Resume an oracle from its saved joint tree

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 33 (the seal), 34 (Ctrl-C), 37 (session record and resume), 38 (per-sentence
checkpoints).
**Blocks:** nothing. Independent of `tactics-run-survives-an-unanswered-interrupt.md`. Whichever
lands second makes a respawned oracle (sealed, then left behind) resumable by this story's rules.
**Records:** `docs/adr/0008-resuming-an-oracle-uses-its-saved-joint-tree.md`.
**Naming:** this story is named, not numbered, so it cannot collide with stories written in
parallel. Refer to it by file name.
**Vocabulary:** `CONTEXT.md` *Saved joint tree*, *Closed node*, *Resume mode*.

---

## 1. Why this story exists

The owner: *"when using the command domino easycrypt prove and resuming a half processed proof
which is mid oracle, I want to save wherever that oracle has progressed and continue from there …
Also allow the user to choose how they want to resume."*

Story 37 resumes an equivalence one oracle at a time. An oracle left `interrupted` is proved again
from the start, lockstep execution included. On kem-dem and 4WHS one oracle can take many
minutes, so a Ctrl-C near its end throws all of that away.

The design session settled these points:

- **Save the joint tree; don't make the debugger deterministic.** Running lockstep execution again
  is not guaranteed to give back the same tree or the same node ids (ADR 0008). The solver options
  do not change.
- **Resume at the node, not the sentence.** Every closed node is kept. The in-flight node is
  proved again from its first rung. Resuming at the sentence would mean recording and replaying
  the ladder's call stack; that option was considered and rejected (ADR 0008).
- **Three resume modes:** `trust` (the default), `replay` and `restart`.

## 2. Inherited from earlier stories

- **Story 37** (`src/easycrypt/job.rs`, `src/easycrypt/tactics/mod.rs`):
  - `SessionRecord` is at version 2. `OracleRecord` has `name`, `status`, `script` (done oracles
    only), `admits`, `lockstep`, and `nodes: Vec<NodeRecord {id, tactics}>`.
  - `nodes` comes from `Script::by_node` (`tactics/script.rs:84`). It groups the accepted
    sentences per node but **drops the bullets, the depths and the interleaving with child
    nodes**, so a node's subtree script cannot be rebuilt from it. This story replaces it.
  - `plan_job` (`mod.rs:574`) returns `JobPlan::{Skip, Prove { prior }}`.
  - `OracleTactics::{from_record, to_record}`. A resumed done oracle gets `admit.` in the live
    session and its `script` in the file (ADR 0006).
- **Story 33/34** (`tactics/driver.rs`): `Prover::seal`/`seal_with` produce a `Sealed` whose `node`
  is the innermost node the walk was in (`N<k>` or `router`). That is the **in-flight node**.
  `Prover::stop_with` seals once and unwinds.
- **Story 38:** under `--write-granularity tactic` (the default), `ProofFile::write` runs after
  every accepted sentence, writing the report, then `Eq_*.ec`, then the record.
- **Lockstep execution:**
  - `tactics_for_oracle` (`mod.rs:953`) calls `run_lockstep_command` first. It gets a
    `LockstepRun { meta, outcome, summary, elapsed }` (`src/debug/lockstep_run.rs:288`) and builds
    `OracleTree::new(&run.outcome)` (`driver.rs:171`).
  - The walk reads `run.meta.goals.relations` (for `unfold_ops`) and `run.summary`. Check whether
    it reads any other field of `meta`.
  - `LockstepOutcome`, `JointTree`, `JointNode`, `PairRecord` and `StuckPoint`
    (`src/debug/lockstep.rs:183`) derive `Serialize` **but not `Deserialize`**.
  - The tree is an arena in depth-first pre-order, and node `k` is `N<k>`.
  - `TacticsOptions::lockstep_timeout_ms` is `None` in `prove`, so it sets no `tlimit-per`.
- **The walk:**
  - `Prover::prove_node(idx)` (`driver.rs:763`) proves the front goal, which is node `idx`'s
    program goal. It tags sentences with `Script::set_node` and checkpoints.
  - `prove_node_inner` tries rung 0 (`auto => /#.` under `timeouts.rung0`) first on every node that
    is not a terminal pair. Then it dispatches on `node.kind`.
  - Children are entered through `ChildOutcome::Explored { node } => self.prove_node(*node)`
    (`driver.rs:895`), inside the bullets the parent opened.
- **ADR 0004/0006:** the session record is protected. `export --force` deletes records. `prove`
  never translates.

## 3. Work to do

### 3.1 Save the joint tree

- Derive `Deserialize` for `LockstepOutcome` and everything it contains, and for whatever part of
  `LockstepSummary`/`LockstepMeta` the walk reads (§2). Don't reconstruct the walk's input by
  parsing `trace.json`: that file is a run artifact.
- In `tactics_for_oracle`, after lockstep execution has finished without being stopped and before
  the first sentence is sent, write `Eq_<L>_<R>.<oracle>.tree.json` beside the session record,
  atomically:

  ```json
  {
    "version": 1,
    "oracle": "PKENC",
    "domino": "<version>",
    "fingerprint": "<hex>",
    "outcome": { … },
    "summary": { … },
    "relations": ["…"]
  }
  ```

- **Fingerprint:** a stable hash (not `DefaultHasher`, whose output may change between Rust
  releases) over everything lockstep execution read for this oracle:
  - the monomorphic code of every package instance reachable from the oracle in **both** games;
  - the game constants of both game instances;
  - the oracle's randomness mapping;
  - the equivalence's state relations, and the invariant and lemma SMT files it uses.

  Exclude the domino version. A change to any of these must change the fingerprint, and anything
  else must not. Find the inputs where `run_lockstep_command` loads them, and hash the loaded form
  rather than file bytes where the loader normalises (for example comments in SMT files).
- The tree file is **protected** like the record (ADR 0004's check covers it). `export --force`
  deletes it alongside the record. `prove --force`, `--force --oracle O` (for `O`) and
  `--resume restart` overwrite it when lockstep execution runs again.

### 3.2 Record closed nodes

- Record version **3**. In `OracleRecord`, replace `nodes` with
  `closed: Vec<ClosedNode { id, script }>`. `script` is the node's whole subtree, in order: its own
  sentences, its children's, and the bullets between them. Store it as lines with depths
  **relative to the node** (as `Script` holds `Line`s), so it can be re-rendered at whatever depth
  the resumed walk reaches the node.
- A node is **closed** when `prove_node(idx)` returns `Ok` and its subtree holds no `interrupted`
  admit (`CONTEXT.md` *Closed node*). An admit with any other reason counts as closed. Record only
  the **outermost** closed nodes: a closed node's closed descendants are inside its script.
- `closed` is written for `interrupted` oracles. For `done` oracles it can be omitted, because
  their `script` already covers everything.
- Read version 2 records as before. Their `interrupted` oracles have no `closed` list and no tree
  file, and fall under §3.5.

### 3.3 `--resume <mode>`

Add the flag to `domino easycrypt prove`: `--resume trust|replay|restart`, default `trust`. It
only affects oracles whose status is `interrupted`. Done oracles are resumed as in story 37 under
every mode. `--force` keeps its meaning and overrides `--resume`.

For an `interrupted` oracle with a tree file:

1. **Load the tree** and skip lockstep execution. If the fingerprint differs from the project's,
   print once per oracle:
   `warning: the saved joint tree of PKENC predates changes to <what changed, if known>; the
   EasyCrypt files may be stale too. Export with --force to start over.` Then carry on with the
   saved tree.
2. **Walk it again** with the record's closed set and its in-flight node:
   - **Closed node:** `prove_node(idx)` short-circuits before rung 0. Under `trust` it sends
     `admit.` for the node's goal. Under `replay` it sends the recorded script sentence by
     sentence. If any sentence is rejected, it undoes back to the node's start, warns, and proves
     the node live from its first rung. In both modes the recorded script goes into the file and
     the recorded admits go into the oracle's stats.
   - **Ancestor of the in-flight node:** run as normal, but **skip rung 0**: the earlier job is
     known to have got past it into a child. Its structural steps run live and produce the
     children's goals.
   - **In-flight node:** proved from its first rung, rung 0 included.
   - **Every other node** (later siblings, nodes the earlier job never reached): proved as
     normal.
3. Checkpoints, writes and the seal behave exactly as in a fresh walk. A stop during a resumed
   walk records the nodes that are closed by then, including those carried over.

Under `restart`, an `interrupted` oracle is proved as story 37 proves it today: lockstep execution
again (overwriting the tree file), from scratch.

### 3.4 Report, page and live line

- **Report:** a resumed oracle reads
  `PKENC: resumed at N7 (12 closed nodes kept, trust)`, followed by the usual per-oracle lines.
  With a stale tree it adds `saved joint tree is stale`.
- **Page:** shows a chip `resumed at N7` and the mode. Closed nodes show as `kept from session
  record` rather than as work of this run.
- **Live line** (story 40): while short-circuiting, the tactic shown is `kept` (trust) or the
  replayed sentence.

### 3.5 Fallbacks

| Situation | Behaviour |
|---|---|
| `interrupted`, no tree file (version 2 record, or the earlier job stopped during lockstep execution) | warn, then `restart` |
| tree file unreadable, or a version this domino does not know | warn, then `restart` |
| stop happened in the router prelude (in-flight `router`) | load the tree, no closed nodes: the oracle is walked from its start, without lockstep execution |
| the walk reaches a node whose id is not in the tree | cannot happen with a loaded tree; treat as a bug (`expect`) |

## 4. Acceptance criteria

- [ ] Ctrl-C in the middle of a kem-dem oracle, after at least one node has closed, then `prove`
      again (default `trust`):
  - [ ] the transcript shows no lockstep execution for that oracle;
  - [ ] each outermost closed node is closed by exactly one `admit.`;
  - [ ] no ancestor of the in-flight node tries rung 0;
  - [ ] the in-flight node is proved from rung 0;
  - [ ] the closed nodes' text in the final `Eq_*.ec` is byte-identical to the earlier job's
        checkpoint.
- [ ] Same with `--resume replay`: the closed nodes' sentences are sent again, and the file is
      byte-identical to the `trust` run's file.
- [ ] `--resume restart`: lockstep execution runs and the tree file is rewritten. No sentence is
      skipped.
- [ ] Changing an oracle's code in a reachable package (without exporting) and resuming prints the
      stale-tree warning and still resumes from the saved tree. Changing an unrelated package
      prints nothing.
- [ ] The fingerprint is equal across two processes and across `cargo build` and
      `cargo build --release` (a unit test on a fixed project).
- [ ] A version-2 record with an `interrupted` oracle resumes by restarting it, with a warning.
- [ ] `export --force` deletes every tree file. Without `--force`, export refuses while tree files
      exist, as it does for records.
- [ ] Every resumed `Eq_*.ec` compiles with `easycrypt compile` (the ADR 0005 test helper).
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.

## 5. How to verify

```bash
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt export --force
$D easycrypt prove --theorem <T> --proofstep 0             # Ctrl-C mid-oracle, after N0's first child closed
jq '.oracles[] | {name, status, closed: [.closed[]?.id]}' _build/easycrypt/<T>/Eq_*.session.json
ls _build/easycrypt/<T>/Eq_*.tree.json
$D easycrypt prove --theorem <T> --proofstep 0             # resumed at N…, trust
$D easycrypt prove --theorem <T> --proofstep 0 --oracle <O> --force --resume replay   # compare files
```

Use kem-dem only. 4WHS and yao stay off-limits for `prove` (overview §7).

## 6. Notes / risks

- **Size.** Under `tactic` granularity the record is rewritten after every sentence, and `closed`
  grows with the proof. It replaces `nodes`, which held the same sentences, so the record should
  grow by no more than the bullet and depth data. Measure it on kem-dem's largest oracle and record
  the result.
- **Trust is trust.** Under `trust` a closed node's script is not re-checked, exactly as ADR 0006
  accepts for done oracles. `replay` is the way to have EasyCrypt check it again.
- **A stale tree** can make the alignment report show mismatches and leave more admits. That is
  the accepted price (ADR 0008).
- **Ancestors run live**, so if an ancestor's structural step now takes a different fallback
  (`prove_blind`), the children's goals may differ from what the closed scripts expect. Under
  `trust` the `admit.` still closes the goal. Under `replay` the rejected-sentence fallback of
  §3.3 applies.

## 7. State handed on

Record in the implementation report:
- the record size on kem-dem's largest oracle (before and after);
- the exact fingerprint inputs, with the loader functions they are taken from;
- whether `LockstepMeta` needed to be saved in full.
