# Story 27 — `domino easycrypt --tactics`: proofs from lockstep execution

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 rows "Lockstep
rules" through "Closing a leaf", §8.1b, §8.1c), `docs/adr/0002-…`,
`docs/easycrypt-interaction-and-branching.md`, `docs/BranchingAlgorithm.pdf` and
`docs/ProvingAlgorithm.pdf`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 19 (base case), 23 (lockstep engine), 26 (session + alignment).
**Blocks:** 28, 29.

---

## 1. Why this story exists

This is the goal the whole second half of the epic serves. Today every oracle bullet is
`+ proc; inline. admit.`. With `--tactics`, Domino proves as much of each oracle as it can:

- it walks the lockstep joint tree;
- it sends each step to a live EasyCrypt session;
- it reads back the goals as JSON;
- it leaves `admit` only where it gives up, labelled with the claim, the invariant relation,
  the stuck point and what Domino itself concluded.

The owner: *"if heuristics fail, we just put admit and delegate it to the user"*, with *"the admit
to be used when we give up be in each split of equal-output and invariant case"*.

## 2. Inherited from earlier stories

- **Lockstep engine** (story 23 report): the joint tree with node kinds `determined`,
  `synchronized`, `split`, `sampling-synchronized`, `sampling-independent`, `stuck` and
  `terminal-pair`; per-pair verdicts for equal-output and invariant, and per-relation
  sub-verdicts; ids `J<n>`/`S<n>`; an iterator/visitor API.
- **Session and alignment** (story 26 report): `send`/`undo_to`/`interrupt`, typed goals, decision
  skeletons, `align` mapping IR labels to EasyCrypt instructions, mismatch kinds, and router
  prelude handling by construction.
- **Skeleton** (story 19): after the base case, the open goals are the oracles' `equivF` goals.
  Select each **by its procedure paths in the JSON**, never by position.
- **EasyCrypt behaviour** (§8.1b):
  - `sp.` consumes assignment prefixes;
  - `if.` gives condition, then and else goals;
  - `if => //` leaves `!abort_flag{1} <=> !abort_flag{2}`, because `inv` is opaque;
  - `rnd` works only on a last instruction;
  - `seq n m : (#pre /\ …)` is accepted.
- **Hand-written style** (§8.1c): `if => //; <sel>: auto => /#`,
  `rcondt {i} ^if; 1: auto => /#`, `seq 1 1 : (#pre /\ ={x}); 1: auto => />`, and at leaves
  `auto => /> &1 &2 *; smt(get_setE mem_set)`.

## 3. Work to do

### 3.1 CLI

`domino easycrypt --tactics [--theorem T] [--proofstep N] [--oracle O] [--ec-timeout <s>]`:

- everything is exported as usual, so the project always compiles;
- only the selected `Eq_*.ec` files get tactics, and with `--oracle` only that oracle's bullet. The
  rest keep `+ proc; inline. admit.`;
- this needs the `cvc5-lib` build (lockstep) and a `-json`-capable EasyCrypt (story 26's
  capability check). Fail early and clearly otherwise;
- plain `domino easycrypt` never runs a solver or EasyCrypt, and its output is byte-identical to
  before;
- **4WHS and yao are off-limits for `--tactics`** (overview §7): it runs lockstep execution.

### 3.2 Per oracle

1. Select the oracle's goal from the JSON and send `proc; inline.`.
2. **Router prelude**, by construction:
   - `sp.` then `if.`;
   - the condition goal gets the closing ladder (§3.5);
   - the both-aborted goal gets rung 0 (§3.3), then the ladder;
   - the then goal is where lockstep begins.
3. Run story 26's alignment of EasyCrypt's current program against the lockstep IR. Mismatches
   are logged, and their nodes use the fallback (§3.4).
4. Walk the joint tree DFS alongside EasyCrypt's goals (§3.3). Each EasyCrypt goal corresponds to
   exactly one joint node. Identify the subgoals a tactic produces **by their kind in the JSON**
   (ambient formula vs. `equivS`, and which branch a program goal is in, from its program head),
   **never by position**. This is what removes the fragile `1,3:` selectors of the hand-written
   proofs.
5. Emit the accepted sentences as the bullet's script, one bullet (`+`) per subgoal, indented by
   depth as `BranchingAlgorithm.pdf` does.

### 3.3 Tactics per joint node

**Rung 0.** Every program goal first tries `auto => /#.` (short timeout). This follows the PDF,
and it closes most abort branches in one step. Skip it where §3.6 says to admit straight away.
Then:

| Joint node | Tactic sequence | Side goals |
|---|---|---|
| any node | `sp.` first, if EasyCrypt's head on either side is an assignment | — |
| determined (side *i*, holds / fails) | `rcondt{i} ^if.` / `rcondf{i} ^if.` | the one-sided goal: `auto => /#`, then the ladder |
| synchronized | `if.` | condition goal: the ladder |
| split, both sides | `if{1}.` then `if{2}.` in each child | a combination lockstep pruned: `exfalso; smt().`, then `auto => /#`, else admit |
| split, one side | `if{i}.` | — |
| synchronized sampling | `seq 1 1 : (#pre /\ x{1} = y{2}); 1: auto.` | — |
| independent sampling | `seq 1 0 : (#pre); 1: auto.` / `seq 0 1 : (#pre); 1: auto.` | — |
| stuck | `admit. (* domino: S<n> … *)` | — |
| terminal pair | the leaf procedure (§3.5) | — |

- `x`/`y` are the `rnd` lvalues from **EasyCrypt's** JSON, via alignment, never our names
  (ADR 0002).
- Plumbing nodes are `determined` and use the same row.
- **`seq` is used only at samplings.** It never swallows the assignments after a sampling: a state
  write among them can falsify `#pre`.
- If `seq 1 1` over a synchronized sampling is rejected because a side's head isn't the sampling
  after `sp`, compute the counts from EasyCrypt's statement list (`seq (k+1) (l+1)` where `k`, `l`
  are the assignments before the sampling). Use the post `#pre /\ x{1} = y{2}` only when those
  `k`, `l` statements write nothing that `#pre` mentions; otherwise admit as stuck with reason
  `seq-post`.

### 3.4 Fallback at a mismatch

Where alignment reports a mismatch, run the PDF's trial procedure on that node:

1. `rcondt{1} ^if; 1: auto => /#`, then `rcondf{1} …`, then `{2}`;
2. then `if => //`;
3. then `if{1}`;
4. for a head `rnd` on both sides, `seq 1 1 : (#pre /\ x{1} = y{2}); 1: auto => /#`.

Take the first that succeeds, each under `undo`. Then re-align the resulting subgoals. If nothing
works, `admit` with reason `program-mismatch`. Count every fallback in the report: after story 26
there should be none.

### 3.5 Closing a leaf, and the ladder

**Fast path.** Try `auto => /> &1 &2 *; smt().`

**Split by meaning.** If the fast path fails, `undo` it and split the goal into its parts:

- **equal-output**;
- the invariant's `params_inv`;
- the abort-flag equality;
- under `!abort_flag`, **one part per state relation** (`Domino_<rel>`), matching story 23's
  sub-verdicts.

Identify the parts from the JSON formula tree (operator paths `inv`, `Domino_<rel>`, the equality
of the result variables), never by conjunct index. `/>` substitutes and reorders, so investigate
how to split **before** simplification: for example `auto.`, then `move =>` with the binders the
JSON reports, then `rewrite /inv /=`, then `split`. Record what works.

**Per part** (following `ProvingAlgorithm.pdf`):

1. unfold (`rewrite /<op>`);
2. introduce quantifiers with `move => v1 … vk`, taking `k` and the names from the JSON binders;
3. `rewrite !get_set_neqE /#`;
4. `smt().`;
5. `smt(get_setE mem_set emptyE <hints>).`, where `<hints>` comes from `ssp.toml`
   `[easycrypt] smt_hints = [...]` (new, optional, per project);
6. **give up**: keep steps 1–2 and `admit. (* domino: J7 invariant/Domino_rel_keys; Domino:
   verified *)`.

**The ladder** (for side goals): `smt()`, then `/#`, then unfold `inv` and `smt()` again, then the
hint list, then admit.

### 3.6 Letting Domino's verdicts steer EasyCrypt

For a goal whose joint subtree has terminal pairs where claim C **fails in Domino**, admit C's
parts at once, without spending EasyCrypt time: reason `domino-fails`, naming the failing `J`.
If every pair below fails both claims, admit the whole program goal at the node.

**Inconclusive** in Domino → still try. **Verified** in Domino but EasyCrypt couldn't close it →
admit with reason `domino-verified-ec-failed`. The report highlights this class, because it is
where better heuristics pay off.

### 3.7 Outputs

- The rewritten `Eq_*.ec`. Only accepted sentences go in; every `admit` carries its label.
- **Final check:** `easycrypt compile` on the written file. If it fails despite the session
  accepting every sentence, write that oracle as `admit` only, and report the discrepancy as a bug.
- `_build/easycrypt/<theorem>/Eq_<L>_<R>.report.txt`, with the same content on stdout. Per
  oracle it lists goals closed and admits by reason (`stuck` with its `S` id, `domino-fails`,
  `domino-inconclusive`, `domino-verified-ec-failed`, `program-mismatch`, `seq-post`), the
  fallbacks used and the time.
- The lockstep artifacts for every translated oracle, written exactly as
  `domino debug --easycrypt` writes them (story 23/24), so every `S`/`J` in an admit has a page to
  open.
- `_build/easycrypt/<theorem>/progress/ec-transcript.jsonl`: every sentence sent, with its full
  response, including undone attempts. Story 28 reads it.

## 4. Acceptance criteria

- [ ] `--tactics` on hello-world (after story 20) and kem-dem-cca-ssp writes `Eq_*.ec` files that
      **compile** with `easycrypt compile`.
- [ ] Every remaining `admit` has a label with reason and id, and the report's counts add up to
      the admits in the file (test).
- [ ] hello-world `UsefulOracle` closes with no admit. If it doesn't, the report says exactly
      which part failed and why.
- [ ] kem-dem: per-oracle counts of closed goals and admits by reason are recorded, and every
      `domino-verified-ec-failed` admit is listed with the goal text (`pp`).
- [ ] No tactic in any generated file names a position taken from our listing (review), and no
      subgoal selector is numeric except where it was derived from the JSON.
- [ ] Two runs on an unchanged project give the same `Eq_*.ec`. If `smt` timing makes that
      impossible, say so and show what differed.
- [ ] Plain `domino easycrypt` output byte-identical; `cargo build/test/clippy --workspace` clean
      (including `--features cvc5-lib`).

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
export DOMINO_EASYCRYPT=<story 25 binary>
cargo build --workspace --features cvc5-lib && D=$PWD/target/debug/domino
cd example-projects/kem-dem/kem-dem-cca-ssp
$D easycrypt --tactics --proofstep 0 --oracle PKENC
cat _build/easycrypt/*/Eq_*.report.txt
cd _build/easycrypt/* && easycrypt compile -I . Eq_*[^s].ec
```

## 6. Notes / risks

- **Every attempt runs under `undo`.** The session state must equal "all accepted sentences so
  far" at every step, or the written file won't replay.
- **Time.** `smt` calls dominate. Rung 0 and the ladder need timeouts (`--ec-timeout`,
  SIGINT through the session), and the report shows where the time went.
- **The leaf split is the least certain part.** If splitting by meaning proves impossible in some
  goal shape, fall back to `auto => /> &1 &2 *` plus `do split` and identify the parts by their
  `pp`. Record the shapes where this happened.
- **Out of scope:** case analysis on table writes, meaning the `case (k = key)` loop of
  `ProvingAlgorithm.pdf` step 4 (story 29), and explicit randomness (story 30).

## 7. State handed to the next story

Record in the report:

- the per-node tactic mapping as implemented, with any deviations from §3.3;
- how the leaf split was done;
- the admit label format;
- the report format;
- the transcript format;
- per-oracle results for hello-world and kem-dem, with timings;
- the list of `domino-verified-ec-failed` goals. They are story 29's input.
