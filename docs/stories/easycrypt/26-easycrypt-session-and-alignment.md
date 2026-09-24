# Story 26 — EasyCrypt session, skeleton alignment, `domino easycrypt --check-alignment`

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 "Tactics take
positions from EasyCrypt", §8.1b) and `docs/adr/0002-tactics-take-positions-from-easycrypt.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** 22 (plumbing branches in the IR), 25 (`easycrypt cli -json`).
**Blocks:** 27.

---

## 1. Why this story exists

Tactic generation needs two things, and this story builds both:

1. **A live EasyCrypt session from Rust:** send a sentence, get typed goals back, undo cheaply.
2. **Alignment:** a way to tie each joint decision of lockstep execution to the EasyCrypt program
   in the current goal. After `proc; inline.`, EasyCrypt's program has the same order and nesting
   as our listing but a different statement list: extra argument and return copies, and
   different names (§8.1b). So statement positions and names can't be carried over (ADR 0002).
   What can be compared is the **decision skeleton**: branches, samplings and ends, with
   assignments ignored.

The owner was worried that mismatches would be frequent. So alignment is **measured** before any
tactic is written: `--check-alignment` runs over every oracle on the testing ladder, **4WHS
included**, which is allowed because it needs no cvc5. Its acceptance bar is zero mismatches.
Alignment also runs automatically before every oracle's translation in story 27; the flag just
exposes it on its own.

## 2. Inherited from earlier stories

- `easycrypt cli -json` (story 25 report): the format `domino-json/1`, documented in
  `easycrypt/doc/json-output.md`, one JSON line per sentence, all goals, full trees with `pp`.
- The IR: `inline_oracle_ec`; `InlStmt::Branch.plumbing` (story 22); `InlStmt::Sample`;
  terminals `Return`/`Abort`. The router prelude and tail are **not** in the IR; handle them by
  construction (story 22 §3.3). `game.rs`'s `router_module_and_flag` and
  `instance_module_names` give the names.
- The generated proof skeleton (`proof.rs`) after story 19:
  - `byequiv (…) => //.`, `proc; inline.`, `call (: inv …); last first.`,
    `auto => />; smt(emptyE map_empty).`;
  - then one `+ proc; inline. admit.` per oracle, in game-interface order.
- EasyCrypt facts (§8.1b):
  - after `proc; inline.` the top level is `ec_result <- None; if (!abort_flag) { … }` plus the
    tail;
  - `sp.` consumes assignment prefixes;
  - SIGINT interrupts and keeps the session;
  - run EasyCrypt **outside** the clone directory (prover pin in `easycrypt.project`).

## 3. Work to do

### 3.1 The session (suggested module `src/easycrypt/session.rs`)

- Locate the binary through `DOMINO_EASYCRYPT`, falling back to `easycrypt` on `PATH`. **Check the
  capability** at startup by sending one harmless sentence and requiring
  `"version": "domino-json/1"`. Otherwise fail with a message naming the variable and story 25's
  branch.
- Spawn `… cli -json -I <export dir>` with the export directory as working directory, and
  typed-deserialize each response line with `serde`. Put the Rust mirror of the format in one
  module, written against `json-output.md`.
- API sketch: `send(sentence) -> Response`, `undo_to(state)`, `interrupt()` (SIGINT on a
  per-command timeout), `goals() -> &[Goal]`. Keep the transcript in memory; story 27 writes it to
  a file.
- Tests skip, rather than fail, when no `-json`-capable binary is available (§7).

### 3.2 Decision skeletons

- **From EasyCrypt:** walk an instruction list from the JSON. `if` becomes a branch node with the
  skeletons of both blocks; `rnd` becomes a sampling node carrying the lvalue's `pp` (the name
  story 27 needs); the end becomes an end node. Assignments are skipped; calls cannot remain after
  `proc; inline.`. Any other instruction (`while`, `match`, …) is an **unknown node**.
- **From the IR:** walk an `InlinedOracle` the same way. `Branch` becomes a branch node carrying
  its `plumbing` kind; `Sample` becomes a sampling node; a terminal becomes an end node. `Call`
  frames are transparent, since after `proc; inline.` EasyCrypt has inlined them too.

### 3.3 Alignment

`align(ec: &Skeleton, ir: &Skeleton) -> Alignment` walks both skeletons in parallel:

- equal kinds match, and branches recurse into then/else;
- **an IR end matches any remaining EasyCrypt suffix on that side**. What follows an IR terminal
  in EasyCrypt is plumbing that the closing step consumes (story 22 §3.3);
- the **router prelude** is peeled off the EasyCrypt side by construction: the known top-level
  shape of the router `game.rs` generates. If that shape isn't found, report a mismatch of kind
  `router-shape`;
- anything else is a **mismatch**, recorded with its kind (`kind-differs`, `extra-ec-decision`,
  `missing-ec-decision`, `unknown-ec-instruction`, `router-shape`), both sides' `pp`/label, and
  the path from the root. After a mismatch, **resynchronise** on the next pair of matching
  sub-skeletons, so one surprise doesn't hide the rest.

The result maps each IR decision label to its EasyCrypt instruction (the `pp`, the lvalue for a
sampling, and the position in EasyCrypt's statement list). Story 27 uses it to build tactics and
to decide when to fall back to trial search.

### 3.4 `domino easycrypt --check-alignment`

`domino easycrypt [--theorem T] [--proofstep N] [--oracle O] --check-alignment`:

1. Export as usual.
2. For each selected equivalence, open a session and feed the `Eq_*.ec` file up to and including
   `call (…); last first.`. **Replace the base case by `admit.`**, so no `smt` runs.
3. For each oracle, pick its goal **from the JSON** (the `equivF` whose procedures are that
   oracle's), not by position, and send `proc; inline.`. Build both skeletons, align them, record
   the result, and `undo` to the state before `proc`. Then admit that goal and move on.
4. Print a report: per equivalence and oracle, `aligned` or the mismatches. The exit status is
   non-zero if there is any mismatch. Write `_build/easycrypt/<theorem>/alignment.txt` too.

Plain `domino easycrypt` is unaffected. It never starts EasyCrypt.

### 3.5 Fix what it finds

Run `--check-alignment` on hello-world, simple-KEM-example, kem-dem-cca-ssp and **all of 4WHS**
(`Simple4WHS`, `Full4WHS`).

- Every mismatch that comes from our lowering is fixed **in the lowering** (story 22's rules)
  within this story.
- A mismatch that is EasyCrypt's own behaviour, such as an instruction kind it introduces, is
  documented in §8.1b of the overview with an example, and alignment learns to accept it
  explicitly.

## 4. Acceptance criteria

- [ ] `--check-alignment` reports **zero mismatches** on every oracle of hello-world,
      simple-KEM-example, kem-dem-cca-ssp, Simple4WHS and Full4WHS. Record the number of oracles
      checked and the run time.
- [ ] Unit tests for `align` over hand-built skeletons cover each mismatch kind and a
      resynchronisation.
- [ ] A test with an EasyCrypt JSON fixture checked in under `testdata/easycrypt/story25/` runs
      without EasyCrypt, so CI covers skeleton extraction from the JSON.
- [ ] The session test, when the binary is present, covers send / error / undo / interrupt.
- [ ] Plain `domino easycrypt` output is byte-identical to before the story.
- [ ] `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
export DOMINO_EASYCRYPT=<clone>/_build/default/src/ec.exe     # from story 25's report
cargo build --workspace && D=$PWD/target/debug/domino
cd example-projects/4WHS && $D easycrypt --check-alignment    # allowed on 4WHS: no cvc5
```

## 6. Notes / risks

- **Don't match names** like `ec_done`, `ec_r*` or `abort_flag` in EasyCrypt's output (ADR 0002).
  The router prelude is known by construction, and everything else is structural.
- Selecting an oracle's goal from the JSON rather than by bullet position also protects against
  story 19's class of bug, where a tactic lands on the wrong goal.

## 7. State handed to the next story

Record in the report:

- the session API;
- the skeleton and alignment types;
- the mismatch kinds;
- the per-project alignment results and timings;
- every lowering fix made;
- any EasyCrypt behaviour alignment had to accept.
