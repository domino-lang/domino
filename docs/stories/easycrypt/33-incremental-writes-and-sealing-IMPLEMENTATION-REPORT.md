# Story 33 — implementation report

## What changed

- **The seal is `Script::sealed(open, label) -> (Script, usize)`** (`src/easycrypt/tactics/script.rs`).
  It works on a copy and sends nothing. It returns the script with every goal the oracle still
  has open closed by `admit. <label>`, and how many admits that took.
  - `Script::enter_bullet(open)` now takes the session's goal count when the block is entered.
    `Script::open_at_entry` keeps one count per open block. From those counts and the count now,
    the seal knows which goals belong to which block:
    - First, the current block's goals. When the block's last tactic left several, each gets a
      `+` bullet one level in. Otherwise the front goal is admitted in the block itself, as a
      `+` bullet if the block has just been opened.
    - Then, block by block outwards, the goals that were waiting behind that block when it was
      entered. Each gets a bullet at that block's level.
    - The goals behind the oracle's own goal belong to other oracles and are left alone.
  - EasyCrypt's bullets do not focus (the export sets no `strict_bullets` pragma), so `n` admits
    close `n` goals wherever they are placed. The placement is only for the reader. A last
    catch-all still admits any goals the counts did not account for, so a sealed bullet always
    closes.
  - Nothing to seal (0 admits, script unchanged) in two cases:
    - before the oracle's first sentence. The writer then keeps the export's
      `+ proc; inline. admit.`, so an untouched oracle stays unlabelled (§3.5).
    - after the oracle's bullet has closed. So the seal at oracle granularity changes nothing.
- **`AdmitReason::Interrupted`**, slug `interrupted`, last in `ALL`. A sealed admit reads
  `admit. (* domino: N<k> open-goal; reason: interrupted; Domino: n/a *)`.
  - `N<k>` is the innermost joint node the walk is in (`router` in the router prelude).
  - The report's by-reason table picks it up with no change.
- **`Prover`** (`src/easycrypt/tactics/driver.rs`) has three new fields:
  - `node: Option<usize>`, the innermost joint node. `prove_node` sets it and restores it.
  - `mismatches: Vec<String>`. This was the return value of `oracle()`, which now returns
    `R<()>`.
  - `checkpoint: Option<&mut dyn FnMut(Sealed)>`.

  It also has two new methods:
  - `seal(&self) -> Sealed { script, stats, mismatches }`, callable between any two sentences.
  - `checkpoint(&mut self)`: seal and hand the result to the checkpoint. `prove_node` calls it
    after every node that returned `Ok`.
- **`ProofFile`** (`src/easycrypt/tactics/mod.rs`) is the equivalence's proof file and its
  report while the run goes on:
  - Its fields: the exported source, the `(oracle, proc)` pairs, `out_dir`, the start time, and
    the `EquivalenceTactics` so far (the finished oracles).
  - `write(in_flight)` renders both, with the oracles in the file's order. It writes the
    **report first, then `Eq_*.ec`**, each through `write_atomically`. That function writes and syncs a
    temporary file `progress/.<name>.tmp`, which is a run artifact, so a leftover one blocks
    nothing (story 32), and then renames it over the target. A reader who sees a file therefore
    finds a report at least as new. A kill between the two renames leaves the report one write
    ahead, never behind.
- **Write points:**
  - `tactics_for_equivalence` writes after every `tactics_for_oracle`, before
    `live.oracle_finished`, and once more at the end. That last write includes the "no goal"
    oracles and gives the final `elapsed`.
  - Under `WriteGranularity::Node`, `tactics_for_oracle` installs `write_sealed` as the prover's
    checkpoint. It turns the `Sealed` into the oracle's `OracleTactics` (`result_of`, which is
    also what builds the final result) and calls `proof.write(Some(&partial))`.
  - The in-flight oracle's report entry is the partial one. Its admits include the
    `interrupted` ones, so the counts match the file.
- **A failed write** (a full disk):
  - At an oracle boundary, it ends the run with `TacticsError::Io`, as before.
  - In node mode, the closure keeps the first error and skips later node writes. The error
    ends the run after the oracle.

  In both cases the last good write stays on disk.
- **`easycrypt compile` is gone from the run** (ADR 0005). The gate, its revert path,
  `OracleTactics::reverted` and the report's `BUG:` line are removed. `compile` moved into
  `tactics/tests.rs` (`mod live`). The two story-27 tests and the new sealed-file test are its
  only callers.
- **CLI:** `--write-granularity <oracle|node>` (requires `--tactics`, default `oracle`).
  - `WriteGranularityArg` in `crates/domino/src/cli.rs` maps to
    `TacticsOptions::write_granularity: WriteGranularity { Oracle (default), Node }`.
- `CONTEXT.md`: *Seal* now says it works on a copy, sends nothing, and labels its admits
  `interrupted`.

## Verification

- `script::tests` (5 new), the seal against hand-computed renders:
  - mid-block, a closed block, a just-opened bullet, subgoals not yet entered;
  - "nothing to seal" before the first sentence and after the oracle;
  - the unsealed script is unchanged.
- `tactics::tests::the_admits_of_a_seal_have_their_own_reason_in_the_report`: `Interrupted`
  is in `ALL`, and the label and by-reason table read `3 admits (stuck 1, interrupted 2)`.
- `overwrite::tests::a_sealed_oracle_counts_as_partially_proved`: story 32's `proof_progress`
  on a sealed bullet gives partial 1 of 2. The bullet shape is unchanged: `(* <proc> *)`, then
  `+ proc; inline.`.
- End to end, `tactics::tests::live` (DOMINO_EASYCRYPT; `hello-world-oracle-rename-new`, two
  oracles, one with a `domino-fails` admit, ~4 s, rung 0 off). A capturing `ExportObserver`
  reads `Eq_*.ec` and the report at every `ItemStarted`/`GoalFinished`/`PhaseFinished`, that is,
  *during* the run.
  - `each_oracle_is_on_disk_as_soon_as_it_is_proved` (**AC 1**):
    - While oracle 1 runs, the file is the untouched export and there is no report.
    - When oracle 2 starts, oracle 1's final script is in the file and the other bullet is still
      untouched. The report names oracle 1 only, and its admit count equals the file's
      labelled admits.
  - `at_node_granularity_every_write_is_a_complete_sealed_proof_and_its_report` (**AC 2, 3, 5**).
    For every mid-oracle capture:
    - `proof_progress` sees both bullets and the file has `qed.`;
    - every `admit.` is labelled, except untouched `+ proc; inline. admit.` bullets;
    - the report's `(admits, interrupted)` equal the file's labelled `(admits, interrupted)`.

    Some capture is sealed. The first and last sealed captures **compile** with
    `easycrypt compile`, run by the test.
  - `sealing_sends_nothing_and_the_final_file_does_not_depend_on_the_granularity` (**AC 4**):
    - The transcripts of an `oracle` and a `node` run hold the same sentences in the same
      order: no `admit.` and no `undo` of a seal.
    - The final `Eq_*.ec` is identical in both runs and has no `interrupted`.
    - No `.tmp` is left in `progress/`.
  - Story 27's `two_runs_on_an_unchanged_project_write_the_same_file` (**AC 8**) and the
    report-equals-labelled-admits test (`an_oracle_that_was_not_asked_for_keeps_its_admit`,
    **AC 7**) are unchanged and pass.
- `crates/domino/tests/easycrypt_tactics_writes.rs` (runs the binary, `cvc5-lib` and
  `DOMINO_EASYCRYPT`):
  - `a_tactics_run_never_runs_easycrypt_compile` (**AC 9**): hello-world with a wrapper
    `ec.native` that logs each invocation and exits 1 on `compile`. The log shows `cli` and
    never `compile`, the proof is written, and no `.eco` appears.
  - `a_run_killed_mid_oracle_leaves_its_last_write_intact` (**AC 6**):
    - The run is `--write-granularity node --no-rung0` on `hello-world-oracle-rename-new`. The
      test polls the file until a sealed write appears, then sends SIGKILL (the exit status
      signal is 9).
    - The file on disk ends in `end section.`, has `qed.`, and has 2 bullets of which at least 1
      is (partially) proved.
    - The report is present and whole, and nothing ends in `.tmp` in the theorem directory.
    - Stable over 3 consecutive runs.
- Seen in a sealed capture (hello-world-oracle-rename-new, after oracle 2's root node):

  ```
  (* d_AnotherUsefulOracle *)
  + proc; inline.
    sp 1 1.
    if.
    + auto => /#.
    + sp 3 3.
      seq 1 1 : (#pre /\ rand{1} = rand{2}); 1: auto => />.
      auto => /> &1 &2 *; smt().
    + admit. (* domino: router open-goal; reason: interrupted; Domino: n/a *)
  qed.
  ```
- **Manual, §5 on kem-dem** (debug build): `--tactics --proofstep 0 --oracle PKENC
  --write-granularity node --out <scratch>`, with a copy of `Eq_*.ec` and its report taken every
  5 s.
  - Before the first node write there were 135 snapshots (about 11 min), all of them the
    untouched export. Nodes finish bottom-up, so the first write comes when the first leaf
    (`N22`) is done, and that leaf took most of the run.
  - Then 5 sealed snapshots. Each has PKENC's walk down to the leaf, 2
    `domino-verified-ec-failed` admits, and 5 `interrupted` admits closing the open blocks at
    depths 6 to 2 (label `N4`). `PKDEC` stays `+ proc; inline. admit.`. The report next to each
    says `7 admits (domino-verified-ec-failed 2, interrupted 5)`.
  - **The first and the last sealed snapshot compile** with `easycrypt compile -I . Eq_….ec`
    (exit 0), run by hand in a copy of the output directory.
  - The run then **died on its own**: `EasyCrypt did not answer `auto => /#.` after being
    interrupted` (story 26's `Unresponsive`, the 2 s rung-0 timeout on the last `both-aborted`
    goal, while the full test suite loaded the machine). **The file on disk after that error is
    the last sealed write**, with 5 `interrupted` admits, together with its report. This is the
    "EasyCrypt dying" case of §1, seen on a real run. The error itself predates this story
    (follow-up: `Unresponsive` under load).
  - The walk had a leftover goal: the seal after `N5` (the first `if{1}` arm) put one admit in
    that arm's own block, in addition to the waiting goals. The arm's goal was still open in the
    session after its subtree returned. So the walk broke its own invariant somewhere in the leaf
    (a `split.` that left more goals than expected is the likely place; `solve_ambient`). The
    seal counts the session's goals, not the walk's intentions, so the file still closed. This
    predates this story and was left alone (follow-up).
- `cargo clippy --workspace --all-targets`, with and without `--features cvc5-lib`: no warnings.
- Full suite, `cargo test --workspace` with `DOMINO_EASYCRYPT=easycrypt/ec.native`:
  - without `cvc5-lib`: all pass (sspverif 507 passed, 5 ignored; domino
    `easycrypt_overwrite` 5, `easycrypt_progress` 1).
  - with `--features cvc5-lib`: sspverif 574 passed, 1 failed, 6 ignored. The failure is the
    known `debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim` (stories 23–32). The
    other targets (`--no-fail-fast`) all pass: `easycrypt_overwrite` 5, `easycrypt_progress` 1,
    `easycrypt_tactics_writes` 2.
- `cargo build --workspace`, with and without `cvc5-lib`: clean.

## Deviations and notes

- **"After every joint node" means after a node's goal is done**, which is when `prove_node`
  returns. Nodes finish bottom-up, so on kem-dem `PKENC` the first node write comes only when the
  first leaf is done, and a leaf can take up to `--leaf-budget` (300 s). If the owner wants to
  watch the path *down* to the first leaf as well, a second `self.checkpoint()` at the top of
  `prove_node` is a one-line change, at the cost of twice the writes.
- **An oracle proved by the fallback** (`prove_blind`, after an alignment mismatch or a failed
  router prelude) has no joint nodes, so node granularity writes it only when it ends. A walk
  that fails with an error gets no further write; the last good one stays on disk.
- Each temporary file is `sync_all`ed before its rename, so a crash cannot leave the file
  empty. The directory itself is not synced.
- The report of a mid-run write lists only the oracles finished so far and the one in flight,
  as the final report never lists oracles that were not asked for. Its last line counts those
  (`1 oracles, …`). A seal after node N finishes is labelled with the node the walk is back
  in (N's parent, or `router`), which is where the remaining goals are. The in-flight oracle gets no line saying it was sealed; its `interrupted`
  admits show it. Story 34 adds the `interrupted: sealed <oracle> …` line.
- Sealed admits are not reported to the live page (`LiveHandle::admitted`). They are not the
  walk's decisions, and the next write replaces them. The page's per-oracle summary comes from
  the final result, which has none.
- `live.activity("easycrypt compile …")` went away with the compile. Writing takes milliseconds
  and shows no activity.
- Story 27's `proc; inline.` refused case writes `+ admit. (* … program-mismatch … *)` directly
  under the `(* <proc> *)` marker. That bullet does not start `+ proc`, so story 32's
  `proof_progress` does not count it as an oracle bullet. This predates this story and was left
  alone (follow-up).
- `rustfmt` would reformat some lines in `tactics/mod.rs`, `driver.rs`, `tests.rs`, `cli.rs`
  and `main.rs`. Those lines are from before this story. Only this story's hunks were formatted.

## State handed to the next story

- **Seal entry point:** `Prover::seal(&self) -> Sealed` (`driver.rs`). It can be called
  between any two sentences. It reads `script` and `session.goals().len()` only and sends
  nothing. The admit id is `Prover::node` (`N<k>`, or `router`).
- **Where a seal can be requested from:**
  - `Prover::checkpoint()` seals and hands the result to `Prover::checkpoint`, the
    `FnMut(Sealed)` field.
  - Today the only caller is `prove_node`, after each node, when the field is set. It is set
    only for `--write-granularity node`, by `tactics_for_oracle`'s `write_sealed` closure.
  - Story 34's signal-driven stop check should live in the prover (after an interrupted
    sentence is rolled back) and call `self.checkpoint()`. For that, story 34 installs the
    closure in both granularities.
  - Everything is consistent at that point. An `Unresponsive` send leaves `session.goals()` at
    the last answered state, and the script holds accepted sentences only.
- **Granularity plumbing:** `TacticsOptions::write_granularity` (`WriteGranularity`) ←
  `--write-granularity` (`WriteGranularityArg`, `crates/domino/src/cli.rs`, mapped in
  `easycrypt()` in `main.rs`).
- **Writing:** `ProofFile::write(in_flight)` writes the report, then `Eq_*.ec`, both atomically
  through `progress/.<name>.tmp`. It is called:
  - after each oracle, before `live.oracle_finished`;
  - at the end of the equivalence;
  - per node through the checkpoint.
- `AdmitReason::Interrupted` (slug `interrupted`) is in `ALL`, last.
- No `easycrypt compile` in a run. `compile` is a test helper in `tactics/tests.rs`.
- Story 34's "Inherited" section has these points.
