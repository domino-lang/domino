# Story 27 — implementation report

## What changed

- New module `src/easycrypt/tactics/` (`pub mod tactics` in `easycrypt/mod.rs`):
  - `mod.rs`: `run_tactics` (per theorem), the per-equivalence session, the per-oracle lockstep
    run, the file rewrite, the `easycrypt compile` check, the report, `read_smt_hints`.
  - `driver.rs`: the `Prover`, which walks the joint tree alongside the session.
  - `script.rs`: the accepted sentences, bullets, indentation, marks for `undo`.
  - `goals.rs`: reading goals from the JSON (kind, program heads, formula shapes).
  - `tests.rs`.
- `domino easycrypt --tactics [--theorem T] [--proofstep N] [--oracle O] [--ec-timeout <s>]`
  (`crates/domino`). Also `--leaf-budget <s>` (default 300) and a hidden `--no-rung0` (for tests).
  Without the `cvc5-lib` build it fails with `TacticsNeedCvc5Lib`; with it, a
  `Session::start` probe runs **before** anything is exported, so a missing or non-`-json`
  EasyCrypt fails early with story 26's message. Plain `domino easycrypt` is untouched: the
  simple-KEM export was diffed byte for byte against the export a pre-session binary wrote, and
  `git diff` shows no change under `src/writers`.
- `ssp.toml` `[easycrypt] smt_hints = ["lemma", …]` (optional; names only, validated; `toml`
  is a new dependency of `sspverif`, already in the lockfile).
- `Session`: `set_transcript_sink`, `set_context`, `timeout()`, `binary()`; answers are read
  **and parsed on a reader thread with a 1 GiB stack**, and `parse_response` has serde_json's
  recursion limit off (`unbounded_depth`). After a few `sp`s a goal nests deeper than 128 and
  the first kem-dem run died with "recursion limit exceeded".
- `check.rs`: `EquivalenceSetup` / `equivalence_setup` / `oracle_of_goal` factored out of
  `check_equivalence` (shared with the tactics), `describe_mismatch`, `sentences_until_call`,
  `ok_or_reject` are `pub(crate)`.
- Fixtures: `testdata/easycrypt/story27/{hello_world,kem_dem}_tactics_report.txt`, the reports of
  the runs below (the kem-dem one has the goal text of every `domino-verified-ec-failed` admit).

## How a run goes

For each selected equivalence: a session, the file up to `call (…); last first.` and the base
case (`auto => />; smt(emptyE map_empty).`; admitted if it fails). Then, front goal by front
goal: an oracle asked for gets `prove_oracle`, any other `admit.`. For an oracle: **lockstep
execution first** (`run_lockstep_command`, artifacts under `_build/debug/…/<oracle>/easycrypt/`
exactly as `domino debug --easycrypt` writes them), then `proc; inline.`, alignment
(`align_goal`), the router prelude, the joint tree. The bullet replaces `+ proc; inline. admit.`
in the file (text replace of the line after `(* <proc> *)`), then `easycrypt compile` checks the
file; if it fails each scripted oracle is compiled alone and the failing ones are written as
`admit` only and reported as `BUG` (never happened).

## The per-node tactic mapping as implemented (state for stories 28, 29)

Every routine handles "the front goal" and leaves it closed with everything else untouched.
A tactic's subgoals are handled front to back, one `+` bullet each, told apart **by kind**
(ambient / `equivS`), verified before use; a shape that is not the expected one rolls the node
back to the fallback. All counts (`sp k l`) and sampled names come from the JSON of the goal in
front.

| Node | Sent |
|---|---|
| root | `proc; inline.`, `sp k l.`, `if.` → [condition, guarded body = node 0, both aborted]. Condition and both-aborted: `auto => /#.`, else the ladder, else `admit` (reason `router`). |
| any node but a terminal pair | rung 0: `auto => /#.` with a 2 s timeout (`min(2 s, --ec-timeout)`) |
| any node | `sp k l.` with `k`, `l` the leading `asgn` counts in EasyCrypt's JSON |
| determined, per side that moved | `rcondt{i} ^if; 1: auto => /#.` / `rcondf{i} …` (decision `then` / `else`). If the side goal does not close in the sentence: `rcondt{i} ^if.`, then a bullet with `close_side_goal` (the ladder, else `admit`). |
| synchronized | `if.`, bullets: condition (`close_side_goal`), then, else |
| split, both sides | `if{1}.` then in each arm `if{2}.`, four children in tree order; a pruned child gets `exfalso; smt().` / `auto => /#.` else `admit` (**untested**: none of the projects has one) |
| split, one side | `if{i}.` |
| synchronized sampling | `seq 1 1 : (#pre /\ x{1} = y{2}); 1: auto => />.` (variants `/#`, plain `auto` tried in that order); `x`, `y` are the lvalues of the `rnd` heads in the JSON. If assignments still precede the `rnd` after `sp`: `admit`, reason `seq-post` (never happens). |
| independent sampling | `seq 1 0 : (#pre); 1: auto => />.` / `seq 0 1 …` |
| stuck | `admit. (* domino: S<n> stuck/<reason> … *)` after rung 0 |
| terminal pair | the leaf procedure |
| unreachable | `exfalso; smt().` else admit |

**Deviations from §3.3, all forced by what EasyCrypt does:**

- **`sp k l.`, not `sp.`.** EasyCrypt's `sp` also consumes an `if` whose condition the
  precondition decides (seen on hello-world: after `seq`, `sp.` swallowed the call-result `if`
  and `rcondt` then failed with `invalid split index: ^if`). Counting the leading assignments
  from the JSON keeps the tree and EasyCrypt's program in step. (§8.1b's "sp consumes assignment
  prefixes" is true for undecided ifs only.) A bare `sp.` is used only at a leaf.
- **`seq … ; 1: auto => />.`, not `1: auto.`**: plain `auto` on the `rnd` goal leaves an ambient
  residual as goal 1 (`forall &1 &2, …`), so the sentence would not close it.
- `rcondt`'s side goal is `forall &m0, hoare[<skip> : … ==> cond]`, not an `equivS`. `reduce_to_ambient`
  introduces `&m0` and runs `auto.` before the ladder.

## The ladder and the leaf split

**Ladder** (`close_side_goal`, atoms): `smt().`; then `move => <binders from JSON> hpre.`, the
invariant unfolded in `hpre` (below), `smt().`; then both again with
`smt(get_setE mem_set emptyE <smt_hints>)`. Give up: `admit`, after keeping `move`/`auto`.

**Unfolding.** `smt()` does see through `inv` when it is a hypothesis of the goal in `=>` form
(`auto => /#` proved the router condition), but not reliably through nested records: the
tactic `rewrite /inv /params_inv /Domino_<rel>… in hpre.` (relation names from the lockstep
meta, `run.meta.goals.relations`) is sent right after the premise is introduced, only when the
JSON hypothesis mentions `inv`.

**Leaf** (terminal pair):

1. Fast path: `auto => /> &1 &2 *; smt().`; then `sp.` + the same; then with the hint list.
   Skipped when Domino says a claim fails at the pair.
2. Split by meaning: `sp.`, `skip => &1 &2 hpre.` (falls back to `auto.` + `move => &1 &2 hpre.`).
   `sp.` finishes the router's tail `if` and `skip` leaves `forall &1 &2, pre => post` with
   `post = equal-output /\ inv …` **exactly as the program wrote it**. `auto.` alone would put the
   tail `if` inside the formula (`let … in if …`), which cannot be split; `auto => />`
   substitutes and unfolds (25 anonymous hypotheses and a flat conjunction of atoms), which loses
   the meaning.
3. `solve_ambient` walks the **formula JSON**: `forall` → `move => <binders>`; `A => B` →
   `move => hpre` (+ unfold); `A /\ B` → `split.`, a bullet each; app with operator leaf `inv` →
   `rewrite /inv.` (part = invariant); `Domino_<rel>` → `rewrite /Domino_<rel>.` (part =
   relation `<rel>`); else an atom (ladder). Parts are never identified by conjunct index.
4. A part that fails in Domino (`GoalFails`, and for the invariant only where no side aborts,
   story 23's note) is admitted without trying: reason `domino-fails`.
5. Time budget (`--leaf-budget`, default 300 s): see "Time".

Shapes where splitting was not possible: none seen; where `sp.` did not reach `<skip> ~ <skip>`
the `auto.` variant is the recorded fallback (never needed on the ladder projects).

## The admit label

```
admit. (* domino: <id> <claim>; reason: <slug>; Domino: <verified|fails|inconclusive|n/a> *)
```

`id` is `J<n>` (a joint path), `S<n>` (a stuck point; claim `stuck/<engine reason>`), `N<n>` (a
joint node) or `router`. `claim` is `equal-output`, `invariant`, `invariant/Domino_<rel>`,
`equal-output+invariant`, `side-goal`, `branch-condition`, `pruned-combination`, `program`, …, with
` (leaf time budget spent)` appended where the budget cut a part off. `slug` is one of `stuck`,
`domino-fails`, `domino-inconclusive`, `domino-verified-ec-failed`, `program-mismatch`,
`seq-post`, and `router` (added: the router prelude's condition and both-aborted goals, where
Domino has no verdict). Reason after EasyCrypt failed: what Domino concluded about the part
over the subtree's pairs (worst wins); a rcond side goal counts as verified (Domino decided the
branch with two solver queries). Every `admit` the walk writes has this label; the untouched
`+ proc; inline. admit.` of oracles not asked for has none, and a test checks the report's admit
count equals the labelled admits of the file.

## The report

`Eq_<L>_<R>.report.txt` next to the file, the same text on stdout:

```
tactics for Eq_A_B.ec (proofstep 0: A ~ B)
  <oracle>: lockstep J joint paths, N nodes, S stuck points (t)
    goals closed: C, K admits (reason n, …) | no admit, fallbacks: F, EasyCrypt time t (U attempts undone)
    admit J1 <claim> [<reason>] Domino: <view>
      goal: <pp>                      (only for domino-verified-ec-failed)
<n> oracles, <c> goals closed, <a> admits, <t>
```

plus `alignment mismatch (fallback used): …` lines and a `BUG:` line if `easycrypt compile`
rejected the script.

## The transcript

`_build/easycrypt/<theorem>/progress/ec-transcript.jsonl`, one object per sentence sent, in
order, **undone attempts and `undo N.` included**:
`{"file": "<Eq file>", "ctx": "<oracle> N<node> <kind>" | "<oracle> router prelude", "sentence": …,
"ms": <EasyCrypt's time>, "response": <the answer line, verbatim, all goals>}`. `response.status`
tells accepted / `error` / `interrupted`; `response.state` is the undo depth (a sentence is
accepted at depth `state`, an `undo N.` returns to `N`). It is large (kem-dem: 549 MB for the
whole theorem; a goal is 100-700 KB of JSON and each sentence prints every open goal).

## Results (debug build, `ec.native`, cvc5-lib, `--leaf-budget 120`)

| project / oracle | joint paths / nodes | closed | admits | fallbacks | EasyCrypt time |
|---|---|---|---|---|---|
| hello-world `UsefulOracle` (rung 0) | 1 / 3 | 3 | **0** | 0 | 0.4 s |
| hello-world `UsefulOracle` (`--no-rung0`, the walk itself) | 1 / 3 | 3 | **0** | 0 | 0.5 s |
| kem-dem `PKGEN` | 2 / 9 | 5 | 0 | 0 | 3.1 s |
| kem-dem `PKENC` | 4 / 43 | 10 | 8 (all `domino-verified-ec-failed`) | 0 | 691 s |
| kem-dem `PKDEC` | 5 / 25 | 3 | 0 | 0 | 1.2 s |

The whole kem-dem theorem: 12 min wall clock, `easycrypt compile` accepts the written file, two
runs of hello-world write the same `Eq_*.ec` (tested; kem-dem was run twice for PKENC with
identical scripts up to the leaf budget, where the cut point moves with timing).

**`domino-verified-ec-failed` list (story 29's input; goal text in
`testdata/easycrypt/story27/kem_dem_tactics_report.txt`)**, all in `PKENC`, on the two paths
J1 and J2 that share their prefix:

1. `rcondf{2}` side goal after the right-hand `Key`-package branch (`pre => !Key.b{hr}`), J1 and
   J2 (one each): the ladder with `inv` unfolded in the premise still fails. Domino proves it
   with the invariant **plus the project's custom SMT assertion** (kem correctness, `custom smt
   in invariant file`), which the exporter does not translate; that is the likely gap.
2. `rcondt{2}` side goal (`k0 = oget ec_r11 /\ …`), J1 and J2: same suspicion.
3. The leaf `invariant` parts of J1 and J2 that the 120 s budget cut off (four admits): the
   parts before them closed by `smt()`, these were not tried. They are budget cuts, not EasyCrypt
   failures, and are labelled so.

Both of the first two need the custom fact; a first heuristic for story 29 is to export
`custom smt` assertions as axioms/`have`s.

## Time

A failing `smt()` costs 4-5 s (EasyCrypt's own limit) and a sentence on a deep goal 10-40 s,
mostly EasyCrypt printing every open goal as JSON: each `sp k l` adds an `exists` to the
precondition, and `split.` at a leaf multiplies the goals printed per sentence by their count.
A leaf split of a dozen parts therefore costs minutes, hence `--leaf-budget`. Rung 0 costs 2 s
per node where it fails (`min(2 s, --ec-timeout)`; EasyCrypt's own limit is 4.3 s). The report
shows EasyCrypt time per oracle; per-sentence times are in the transcript's `ms`.

## Verification

- Tests (`easycrypt::tactics`): 15, of which the live ones need `DOMINO_EASYCRYPT` and
  `--features cvc5-lib` and skip otherwise: hello-world closes with no admit, compiles, report
  and transcript; the walk alone (rung 0 off) with the tactics per node; the fallback with an
  alignment mismatch on the real session; two runs write the same file; an oracle not asked for
  keeps its admit and the labelled admits equal the report's count; Domino's verdict steering
  (claim, relation, abort exemption); label format; report counts; `smt_hints` parsing;
  script bullets and marks; goal helpers on the recorded fixture.
- `cargo build/clippy --workspace --all-targets`, with and without `--features cvc5-lib`: clean.
- Full suite (`DOMINO_EASYCRYPT` set): `cargo test -p sspverif --lib` 457 pass, 5 ignored;
  `--features cvc5-lib` 519 pass, 6 ignored, **1 failure that predates story 23**
  (`debug::driver::tests::goal_smt_is_empty_for_an_admitted_claim`); the other workspace crates
  and doctests pass.
- Code review (standards and spec, two parallel reviews). Fixed: the misplaced doc comment, the
  redundant clones in `check_equivalence`, a redundant sort, the base `smt` lemma names as a
  const. Left on purpose: (1) the fallback is per oracle (alignment mismatch) or per node
  (primary tactic did not apply), not "re-align the subgoals"; its trial order is
  `rcondt{1}`, `rcondf{1}`, `{2}`, then `if.` (the condition goal goes through the ladder, which is
  what `if => //` plus a bullet is) then `if{i}` then `seq`; (2) `seq (k+1) (l+1)`: not needed,
  because `sp k l` has already consumed every leading assignment when a sampling is reached, so
  the `seq-post` admit is a guard that never fired; (3) the ladder's `/#` rung is the
  `move => <binders> hpre` variant; (4) the side goals of `rcond` and the router prelude are
  labelled `domino-verified-ec-failed` / `router` without a per-part Domino verdict (Domino
  decided the branch by two solver queries, and has no verdict for the prelude); (5) no guard
  against `--tactics` on 4WHS/yao beyond the help text and this report; (6) the added reason
  `router`, `--leaf-budget`, hidden `--no-rung0` are deliberate additions; (7) `Prover` and
  `run_tactics` take many parameters; a context struct is the refactor if a third caller
  appears.

## Open issues / notes

- The pruned-combination tactic (`exfalso; smt().`) and the `unwrap` heads are untested.
- `--tactics` on 4WHS and yao was **not** run (hard rule).
- `Session` drops all but the newest answer's goals from memory; only the transcript file keeps
  them, so it is the largest artifact of a run. Disk space matters: the machine this ran on hit
  "No space left on device" once, which `--tactics` turned into an `io error talking to
  EasyCrypt`.
- The leaf budget makes the result depend on timing on kem-dem (which part is cut off);
  `--leaf-budget` large enough removes it at the price of minutes.
- The fallback (§3.4) is the PDF's trial procedure without the tree, used at a node whose
  primary tactic did not apply, and for a whole oracle whose alignment reports a mismatch. It
  has not been needed on any project of the ladder (0 fallbacks).
