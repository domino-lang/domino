# Story `resume-an-oracle-from-its-saved-joint-tree` — implementation report

## What changed

- **`src/debug/lockstep.rs`, `driver.rs`, `effect.rs`, `lockstep_run.rs`** (§3.1)
  - `LockstepOutcome` and everything in it now derive `Deserialize`, and so does
    `LockstepSummary`. That covers `JointTree`, `JointNode`, `PairRecord`, `StuckPoint`,
    `ClaimVerdict`, the effects and the summary's parts.
  - Two fields stay `&'static str`: `StuckPoint.side` and `VerdictCombo.verdicts`. A new alias
    `StaticStr` reads them back through `side_of` and `verdict_slugs`, which map each value to
    the matching static string.
  - `ClaimVerdict.relations` is omitted when empty.
  - `LockstepMeta` is **not** saved. The walk reads two things from it:
    - `meta.goals.relations`, by name only (for `unfold_ops`). The saved tree keeps those names.
    - `meta.out_dir`, for the page's link to the debug folder. On resume, the page links the
      oracle's `!debug!` folder when its `index.html` is still there.
- **`src/debug/lockstep_fingerprint.rs`** (new): `Fingerprint::of(project, theorem, proofstep,
  oracle)`.
  - It is FNV-1a over 128 bits: no dependency, no hash seed, no `HashMap` order. Each part is
    hashed on its own; the overall hash is taken over the lines `name=hex`.
  - `changed_from` names the parts that differ. `describe_part` gives the words the warning uses.
  - The inputs and their loaders are listed under *State handed to the next story*.
- **`src/easycrypt/job.rs`**
  - **Record version 3.** `OracleRecord.closed: Vec<ClosedNode { id, script: Vec<ScriptLine {
    depth, bullet, sentence, comment }>, admits }>` replaces `nodes`. Depths are relative to the
    node's first line. A v2 record's `nodes` is ignored when read.
  - `OracleRecord.tree_id` names the saved tree the closed nodes were proved on. Both `closed`
    and `tree_id` are written for `interrupted` oracles only.
  - `OracleRecord::in_flight()` returns the node of the `interrupted` admit.
  - `SavedTree` is `Eq_<L>_<R>.<oracle>.tree.json`.
    - Fields: `version` 1, `oracle`, `id` (new for every tree written: time and pid), `domino`,
      `fingerprint`, `fingerprint_parts`, `outcome`, `summary`, `relations`. Name from
      `saved_tree_name`.
    - `SavedTree::read` returns `Ok(None)` when there is no file. It returns an error when the
      file cannot be read, does not parse, or has an unknown `version`; the version is checked
      before the rest is parsed.
  - `remove_session_records` is renamed `remove_records_and_trees`. It also deletes
    `*.tree.json`, so `export --force` deletes the trees. ADR 0004's check already refused any
    unknown file, so a tree file blocks translation.
- **`src/easycrypt/tactics/script.rs`** (§3.2)
  - `node_start` / `close_node` mark a node's span of lines.
  - `closed_nodes()` returns the outermost closed nodes, each with its lines at relative depth and
    its admits.
  - `push_closed` writes a kept node back at whatever depth the walk reaches it. Its first line
    takes the pending bullet.
  - `rollback` drops marks inside an undone attempt.
- **`src/easycrypt/tactics/driver.rs`** (§3.3)
  - `Resume { mode, closed, skip_rung0, reached, kept, replaying }`.
    - `Resume::new` maps the record's ids onto the tree. An id not in the tree panics, which §3.5
      calls a bug.
    - It also records the ancestors of the in-flight node (`OracleTree::ancestors`).
  - `prove_node`:
    - **Closed node** (`keep_node`), sent with `send_unscripted`, which does not script it:
      - `trust` sends `admit.`, and the live line shows `kept`.
      - `replay` sends the recorded sentences. If one is rejected, or the goal is not closed, the
        replay warns, undoes to the state before, and proves the node live from rung 0.
      - Either way the recorded lines go into the script (`push_closed`) and the recorded admits
        into the stats.
    - **Ancestors of the in-flight node** skip rung 0.
    - Every node that returns `Ok` gets `close_node`.
  - The seal also writes into `closed` the record's closed nodes the walk has not reached yet.
    `reached` and `kept` are rolled back with an undone attempt.
  - While a closed node is replayed, a stop or an unanswered interrupt seals with the goal count
    from before the node (`Resume.replaying`), so the checkpoint stays consistent and the node
    stays closed (review fix).
  - Each kept `admit.` and each replayed sentence goes into the transcript under its own node:
    `"<oracle> N<k> <kind> (trust|replay)"`.
- **`src/easycrypt/tactics/mod.rs`**
  - `ResumeMode { Trust, Replay, Restart }` with `slug()`, and `TacticsOptions.resume` (default
    `Trust`).
  - `tactics_for_oracle` now starts with `resuming(…)`. For an `interrupted` oracle under
    `trust`/`replay` it returns the saved tree and the closed nodes, or `None` with a warning.
    Otherwise `lockstep(…)` runs lockstep execution and `save_tree(…)` writes the tree
    atomically before the first sentence.
  - Fallbacks: each of these warns and proves the oracle from the start:
    - a version 2 record;
    - no tree;
    - an unreadable tree, or one of an unknown version;
    - the tree of another oracle;
    - a tree whose `id` is not the record's `tree_id`.
  - A stale fingerprint warns once per oracle and carries on.
  - `save_tree` computes the fingerprint inside `without_custom_smt_warning`
    (`gamehops/equivalence/smtrewrite.rs`). Lockstep execution has just warned about custom SMT in
    the invariant file, and a second load would print it again.
  - `OracleTactics` gains `closed`, `tree_id` and `resumed_at: Option<ResumedAt { node, kept,
    mode, stale }>`.
  - **Report:** `Branch: resumed at N3 (1 closed node kept, trust)`, and
    `; saved joint tree is stale (code)` when the fingerprint differs.
- **`src/easycrypt/tactics/live/`**: the chip `resumed at N3 (trust)`. Kept nodes show
  `kept from session record`, and the step reads `kept`.
- **`crates/domino`**
  - `prove --resume trust|replay|restart`.
  - The help of `--force` says it overrides `--resume`. Translation's `--force` help mentions
    `*.tree.json`.
- **Tests**
  - Test project `testdata/easycrypt/resume/two-branches`: one oracle `Branch` with an if/else,
    each branch a sampling. It is stopped at `goal N1`: N1 closed, N3 in flight.
  - Unit tests in `job.rs`, `script.rs` and `lockstep_fingerprint.rs`, plus one render test.
  - Seven live tests in `tactics::tests::live`.
  - One CLI test in `crates/domino/tests/easycrypt_overwrite.rs`.
- **Docs:** inherited facts were added to stories 44 and 45 (§2).

## Verification

Full suites, final code, `DOMINO_EASYCRYPT=<worktree>/easycrypt/ec.native`:

| Binary | `cargo test --workspace` | `--features cvc5-lib` |
|---|---|---|
| lib (`sspverif`) | 597 passed, 5 ignored | 695 passed, 6 ignored |
| `debug_all_claims` | 3 | 4 |
| `easycrypt_ctrl_c` | 0 | 4 |
| `easycrypt_lockstep_progress` | 0 | 1 |
| `easycrypt_overwrite` | 7 | 7 |
| `easycrypt_progress` | 1 | 1 |
| `easycrypt_prove` | 0 | 5 |
| `easycrypt_tactics_writes` | 0 | 3 |
| `sspverif_smtlib` | 2 | 2 |

Neither run had a failure (209 s and 297 s). Before the final runs, every resume test (the
seven live tests, and the `job`/`script`/fingerprint unit tests) was run on its own after each
change, and none failed except where described here. The new stop-during-replay test was first
run against the code without the review fix, and it failed as expected: `cannot save an incomplete
proof`. An earlier version of the trust/replay test hard-coded the replayed sentences wrongly, and
a first attempt on the two-oracle project hit the `router` in-flight case. Both were test errors
and were fixed before these runs.

`cargo clippy --workspace --all-targets`, with and without `cvc5-lib`, shows only the warnings
that predate this story: `src/debug/sweep.rs:199`, plus the ten `TempDir::into_path`
deprecations with `cvc5-lib`. The new file `lockstep_fingerprint.rs` is rustfmt-clean.

**Acceptance criteria (§4)**

- **Resumed under `trust`:**
  - On two-branches: `a_resumed_oracle_keeps_its_closed_nodes_under_trust_and_replay_alike`.
    - The resumed job runs no lockstep execution for `Branch`.
    - Each closed node gets exactly one `kept` sentence. The transcript records it as `admit.`
      under `Branch N1 … (trust)`.
    - N0, the ancestor, starts with `sp 2 2.`, not rung 0. N3, the in-flight node, starts with
      `auto => /#.`.
    - The closed node's lines in the final `Eq_*.ec` are identical to the checkpoint's.
    - The file compiles.
  - **On kem-dem (by hand, `PKENC`, the largest oracle: 43 nodes):**
    - The first job was stopped with `SIGINT` after 500 s, at N34–N35. The record held
      `PKENC interrupted`, `closed` = [N5] (52 lines, 2 admits), in-flight N34.
    - The resumed job (`trust`, 411 s, run alongside the replay below) printed
      `PKENC: resumed at N34 (1 closed node kept, trust)`. The transcript has no lockstep
      execution.
    - N5 was closed by one `admit.`.
    - N34's 16 ancestors each began with their structural sentence (`sp …`, `if.`, `rcond…`),
      never `auto => /#.`. N34 began with `auto => /#.`.
    - N5's 52 lines in the final file are identical to the checkpoint's.
    - `ec.native compile` of the final file succeeded (37 s).
- **`--resume replay`:**
  - On two-branches the same test checks two things. The recorded sentences are sent again right
    after N1 is entered, and the final file is identical to the `trust` run's.
  - On kem-dem, N5's block is identical between the two runs, but the whole files differ in one
    place. Under `replay`, the live leaf J2 (N40, after the in-flight node) spent its 300 s leaf
    budget differently and was split into two admits, where `trust` had one. Both runs were
    proving N40 live, and they ran concurrently. This is the time budget of a live node, not the
    kept nodes. That run also predates the per-node transcript context, so its 52 replayed
    sentences were logged under `PKENC N4 split`.
- **`--resume restart`:** `restart_runs_lockstep_execution_again_and_rewrites_the_tree`.
  Lockstep execution runs, no `kept` sentence is sent, and the tree is rewritten.
- **Stale tree:** `a_stale_tree_is_walked_and_said_to_be_stale`. Resuming from a tree whose code
  part differs gives the report line `…; saved joint tree is stale (code)` and still uses the saved
  tree. Edits to the code itself are covered by the fingerprint tests:
  - `the_fingerprint_names_the_part_that_changed`: code, invariants, randomness;
  - `code_the_oracle_does_not_reach_is_not_in_its_fingerprint`: a package only another oracle
    reaches, and an uncalled oracle of a reached package, change nothing.
- **Stable fingerprint:** `the_fingerprint_is_stable_and_ignores_where_code_stands` pins the hex
  `68cf6f91…` for a fixed project. It also checks that moving and re-indenting code changes
  nothing. The test passed under `cargo test` and also under `cargo test --release` (run once, for
  this criterion; nothing else was built in release).
- **Version 2 record and other fallbacks:**
  `an_oracle_without_its_tree_or_from_a_version_2_record_is_proved_from_the_start`. It covers no
  tree file, a v2 record, and a record whose `tree_id` names another tree.
- **`export --force`:** `a_saved_joint_tree_blocks_translation_and_force_deletes_it`, plus the
  `job.rs` removal test.
- **Compiles:** the trust/replay test, the stop-during-replay test and the kem-dem file.
- Also covered:
  - `a_closed_node_whose_replay_is_rejected_is_proved_again`;
  - `a_stop_while_a_closed_node_is_replayed_keeps_it_closed_and_seals_its_goal`, which fails
    without the review fix: the checkpoint does not compile;
  - `an_oracle_sealed_by_an_unanswered_interrupt_is_resumed_by_the_next_job`: FOUR_ORACLES, oracle
    2 left unanswered, then resumed at N0 with nothing kept.

## Deviations and notes

- **Seams not confirmed with the user.** The `tdd` skill asks for the seams to be agreed first.
  This ran as a delegated agent with no user to ask, so I took them from the story:
  - the record and tree (`job.rs`);
  - the script marks (`script.rs`);
  - the fingerprint;
  - the resume walk, through `run_tactics_observed` on a small project.
- **What the `code` part hashes.** The story asks for "the monomorphic code of every package
  instance reachable from the oracle". The `code` part hashes something narrower: each side's
  inlined EasyCrypt listing of the oracle (`inline_oracle_ec`), with its signature. That is the
  code the oracle can execute.
  - An uncalled oracle of a reached package therefore changes nothing. This matches "anything else
    must not", and a test pins it.
  - The listing is the `EasyCryptTransform` form. Lockstep execution runs on the `DebugTransform`
    form of the same packages; any change in the code shows in both.
- **The record and tree are linked by `tree_id`** (not in the story). Lockstep execution can run
  again under `--resume restart` or after a fallback. A job killed between writing the new tree
  and the record would otherwise leave the old closed nodes beside a tree they were not proved on.
  Their node ids would then mean something else. Instead, the next job warns and restarts.
- **More fallbacks than §3.5 lists**, each warning and restarting or proving live:
  - a tree file that names another oracle;
  - a closed node holding an admit reason this Domino does not know: that node is proved live;
  - a fingerprint that cannot be computed: the tree is not saved and an old one is removed.
- **`ClosedNode.admits`** (not in §3.2's `{ id, script }`) carries the node's own admits. That is
  how "the recorded admits go into the oracle's stats". A kept admit has no goal text, so its
  `goal:` line in the report is empty. Story 37's resumed done oracles show the same.
- **Router in-flight.** When the in-flight node is `router`, nothing skips rung 0. Any closed nodes
  in the record are still kept. §3.5 expects none there.
- **The seal keeps closed nodes not yet reached**, so a stop during a resumed walk loses none
  (§3.3.3).
- **`from_record` reports `nodes: 0`** for a resumed done oracle. It used to report
  `record.nodes.len()`, a field that no longer exists. The node count of a resumed done oracle
  was never shown.
- **§5's last command contradicts §3.3.** `--oracle O --force --resume replay` restarts O, because
  `--force` overrides `--resume`. To compare `replay` with `trust`, I resumed a copy of the
  interrupted export with `--out` instead.
- **Size (§6, §7).** The kem-dem record above, with PKENC interrupted and N5 closed (52
  sentences), is 7 976 bytes. The same record holding those 52 sentences in v2's
  `nodes: [{id, tactics}]` shape would be 3 228 bytes. `closed` alone is 4 995 bytes against
  1 400. The growth is the per-line `depth`/`bullet` keys and the node's two admits, multiplied by
  pretty-printing one object per line.
  - That is under 8 KB. The record is rewritten after each sentence: a done PKENC record is
    4 870 bytes.
  - A v2 record held every node's sentences, not just the closed ones, so a real v2 record would
    have been somewhat larger than 3 228 bytes.
  - The saved tree is 29.6 KB, and it is written once per lockstep execution.

## State handed to the next story

- **Fingerprint inputs (§7), per side (left, right of the proofstep's equivalence):**
  - `code`:
    - `EasyCryptTransform.transform_theorem(theorem)`, then
      `writers::easycrypt::lower::inline_oracle_ec(instance, oracle)`;
    - hashes `args`, `return_type` and `listing.text`.
  - `constants`: from the untransformed `Theorem::find_game_instance(side)`, the instance name,
    `types` and `consts` (name, type, value).
  - `randomness`:
    - `Equivalence::randomness_by_oracle_name(oracle)`;
    - the SMT of `EquivalenceContext::emit_randomness_mapping_condition(oracle)` and
      `emit_auto_randomness(oracle)`.
  - `invariants`: `EquivalenceTransform.transform_theorem`, then `EquivalenceContext::new` and
    `load_invariants(project)`, then the SMT of `emit_invariant()`. This is the loaded and
    rewritten form, so comments and layout in the `.smt2` files do not count.

  None of them includes a source position. The Domino version is not hashed.
- `LockstepMeta` is not saved in full. Only the relation names are saved (see *What changed*).
- `SavedTree::VERSION` is 1 and `SessionRecord::VERSION` is 3. A future change to
  `LockstepOutcome`'s serialized shape must bump `SavedTree::VERSION`. An unknown version restarts
  the oracle with a warning.
- `TacticsOptions.resume` and `ResumeMode` are public. `ResumedAt` is on `OracleTactics`.

## Notes for follow-up

- The resume warnings are plain `eprintln!`, not `eprintln_above_bars`, so they can tear a live
  bar. That covers no tree, the v2 record, a stale tree, a rejected replay, an unsaved tree and a
  mismatched `tree_id`. Story 44's stage messages are the place for them; this is noted in its §2.
- The `constants` part has no sensitivity test. `code`, `randomness` and `invariants` each have
  one.
- The repo as a whole is not rustfmt-clean (`cargo fmt --check` lists about 490 hunks before this
  story), so only the new file was formatted.
- Review judgement calls left as they are:
  - node ids are `N<k>`/`router` strings, not a type, as in the rest of the tactics code;
  - fingerprint part names are strings, not an enum;
  - `in_flight()` compares the record's reason string, because the record layer holds strings;
  - `Resume.skip_rung0` could be called `ancestors`;
  - `tactics/mod.rs` keeps growing, and a `resume` submodule could take `resuming`, `lockstep`
    and `save_tree`.
