# Story 19 — all-claim runs, and `domino debug` as a Domino-only command

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `00-overview.md`.
**Depends on:** stories 04 (assumption/goal split), 06 (sequential driver), 23 (lockstep engine).
**Supersedes:** `00-overview.md` §3 rows *Claim scope* and *Assumptions*, and
`docs/stories/easycrypt/00-overview.md` §2's `domino debug --easycrypt` row.
**Records:** `docs/adr/0003-all-claim-runs-and-the-strategy-listing-split.md`.

---

## 1. Why this story exists

Two unrelated frustrations, one cause.

**You cannot run the debugger without knowing the answer first.** `--proof`, `--proofstep`,
`--oracle` and `--claim` are all required. To find out what is broken in a project you have to
already know which claim of which oracle of which proofstep to ask about — so the tool that exists
to tell you where a proof breaks cannot be pointed at a proof.

**One claim per run throws the expensive part away.** The cost of a run is the symbolic
exploration: inlining both oracles, enumerating left paths, asking the solver which right branches
are reachable. The claim check at a terminal pair is one `check-sat` on top of work already done.
Today each claim pays for its own exploration, because the claim's dependencies sit in the **base
frame** (`driver.rs:778`) and therefore change which branches get pruned. Three claims, three
identical explorations.

The fix for the second is the enabler for the first: move the dependencies out of the base frame,
and one exploration serves every claim of the oracle.

Separately, `domino debug --easycrypt` conflates two independent things — the **strategy**
(sequential exploration vs lockstep execution) and the **listing** (Domino code vs EasyCrypt code).
This story splits them and puts each on the command where it belongs.

## 2. What changes

### 2.1 `domino debug` becomes a Domino-listing command with two strategies

```
domino debug                    sequential exploration, Domino listing   (today's default)
domino debug --lockstep         lockstep execution,     Domino listing   (new CLI surface)
```

`--easycrypt` is **deleted** from `domino debug`. The engine already supports the Domino listing
(`ListingKind::Domino`, `lockstep_run.rs:440`) — it is `#[allow(dead_code)]` and reachable only
from the engine tests.

### 2.2 EasyCrypt debugging moves to `domino easycrypt --debug`

```
domino easycrypt --debug        lockstep execution, EasyCrypt listing
```

It joins `--check-alignment` and `--tactics` in the `ec_mode` arg group, and is the path
`--tactics` already uses internally. **Claims have no meaning there**: EasyCrypt has no `no-abort`
and no project lemmas, so this mode keeps its no-dependency claim set and takes no `--claim`.

### 2.3 All four filters become optional

`--proof`, `--proofstep`, `--oracle`, `--claim` — omitted means *all*, given means *only that*,
exactly as `domino prove` already does (`cli.rs:246-252`). A run with no `--claim` is an
**all-claim run**.

## 3. Decisions settled in the interview — do not relitigate

| Topic | Decision |
|---|---|
| **Where assumptions live** | With `--claim C`: `C`'s dependencies stay in the base frame, pruning as today — lemmas help prune, and a narrowed run should get that benefit. Without `--claim`: the base frame carries **only** what every claim shares (main / per-game / per-package invariants on the old states, the randomness-mapping condition, `emit_auto_randomness`), and each claim's own dependencies are asserted **at the terminal pair**. |
| **Claim set of an all-claim run** | The full obligation set: the oracle's proof tree (`proof_tree_by_oracle_name`) plus the generated package/game invariant claims (`generate_game_or_package_invariant_claims`) — the same set `prove` discharges. Admitted claims are listed, never checked. |
| **Dependency semantics** | Each claim keeps its **own declared dependencies**, `no-abort` and project lemmas included. The goal is verdicts that are directly comparable to `prove`, not a stricter check. |
| **Path-condition reuse** | One exploration per oracle serves every claim. The pair's path conditions and the shared assumptions are asserted **once**; each claim is one `push` / `check-sat` / `pop` on top, differing only in its own dependencies and its negated goal. Claim count must not multiply the exploration. |
| **No fifth verdict** | `Unreachable` already means *infeasible under the assumptions in force*, and today those include the claim's dependencies. Moving them to the terminal pair does not create a new concept; it gives `Unreachable` a **scope**. `Verdict` stays four variants and gains a *reason*. |
| **Strategy vs listing** | Orthogonal axes. `domino debug` is Domino-listing only; the EasyCrypt listing is reached only through `domino easycrypt`. Sequential-on-EasyCrypt is explicitly **out of scope** and not wanted. |
| **`--tactics` is frozen** | `run_lockstep_command`'s signature and goal construction do not change. `--tactics` output on every acceptance project must be byte-identical before and after this story. |
| **Agreement with `prove`** | An acceptance criterion, not an aspiration. See §5. |

## 4. Work to do

### 4.1 CLI — `crates/domino/src/cli.rs`, `crates/domino/src/main.rs`

`Debug`: `proof: Option<String>`, `proofstep: Option<usize>`, `oracle: Option<String>`,
`claim: Option<String>`. Delete `easycrypt: bool` and every `conflicts_with = "easycrypt"`. Add:

```rust
/// Advance both oracles together and resolve each decision jointly, as an
/// EasyCrypt proof would, instead of exploring the left oracle and then the
/// right one under each of its paths. Domino code either way — for the
/// EasyCrypt listing use `domino easycrypt --debug`.
#[clap(long)] pub(crate) lockstep: bool,
```

`--proofstep` without `--proof` is an error, as in `prove` (`main.rs:150`). A swept theorem whose
proofsteps include reductions or conjectures **skips** them with a one-line note on stderr rather
than erroring — today `equivalence_of` (`driver.rs:~720`) returns `ProofstepNotEquivalence`; that
error stays for an explicitly named proofstep and becomes a skip when sweeping.

`Easycrypt`: add `debug: bool` to the `ec_mode` group, plus `--debug-timeout` mirroring
`--ec-timeout`. Nothing else: `--smt`, `--max-paths`, `--transcript` and `--progress` are not
exposed there, and the internal options are hard-coded exactly as `tactics/mod.rs:529` does today,
so the two paths cannot drift.

### 4.2 The base frame and the per-pair check — `src/debug/driver.rs`

`base_frame` gains a mode. Split it:

```rust
/// Everything every claim of this oracle shares.
fn shared_base_frame(eqctx, oracle) -> Vec<SmtExpr>;   // through emit_randomness_mapping_condition
/// `shared_base_frame` + `emit_claim_assumptions(claim, oracle)` — today's frame.
pub(crate) fn base_frame(eqctx, oracle, claim) -> Vec<SmtExpr>;
```

A single-claim run asserts `base_frame`; an all-claim run asserts `shared_base_frame`.

The solver stack, all-claim, sequential:

```
level 0   shared_base_frame
level 1   left path P            (decls, constraints, return_constraint)
level 2   right path Q           + pair vacuity check-sat
            unsat  -> every claim on this pair is Unreachable { reason: PairInfeasible }; skip
level 3   per claim C, in obligation order:
            assert emit_claim_assumptions(C, oracle)
            assert emit_claim_goal_negated(C, oracle)
            check-sat
          pop
```

Level 0 through 2 are paid once and reused by every claim: that is the whole point of the story.
With `--claim C` the frame at level 0 is `base_frame(.., C)` and level 3 asserts the negated goal
alone — byte-identical to today.

**Obligation order** for level 3: `equal-aborts`, `same-output`, `invariant`, then the rest of the
proof tree in declaration order, then the generated invariant claims. Not cheapest-first: the
report should read like `prove`'s.

**A claim that has already failed keeps being checked** on later pairs — knowing *which* paths
break a claim is the product. `--first-failure-per-claim` stops checking a claim after its first
`GoalFails`, for large sweeps.

### 4.3 `Unreachable` gains a reason — `src/debug/driver.rs:426`

```rust
pub enum Unreachability {
    /// The pair itself cannot happen: the vacuity check at level 2 was unsat.
    PairInfeasible,
    /// The pair happens, but this claim's premise is false on it. `dependency`
    /// names the one that failed, e.g. `no-abort`.
    DependencyFalse { dependency: String },
}

Unreachable { reason: Unreachability },
```

`slug()` stays `"unreachable"`; `trace.json`'s schema version bumps.

**Deciding `DependencyFalse` costs nothing for the dependencies that matter.**
`build_no_abort` (`patterns/relations/no_abort.rs:71`) is `left_no_abort ∧ right_no_abort` over the
two return values' abort constructors, and at a terminal pair the driver already knows both
terminals syntactically (`Terminal::is_abort()`). So, with no solver call at all:

| dependency | false exactly when |
|---|---|
| `no-abort` | either side aborts |
| `left-no-abort` | the left side aborts |
| `right-no-abort` | the right side aborts |
| `equal-aborts` | exactly one side aborts |

That covers all three default claims (`parser/theorem.rs:1140`) and every generated
`package-invariant!…!` / `game-invariant!…!` claim. Check these **before** the goal query and skip
it entirely.

A claim depending on a project lemma or a user relation needs one extra `check-sat` on
`deps ∧ path_l ∧ path_r` — but **only when its goal check came back `unsat`**, since a `sat` goal
check already proves the dependencies satisfiable. Verified pairs are the common case, so run the
extra query lazily.

The reason must reach the reports: *"unreachable — left aborts at L27, and this claim assumes
no-abort"* is the line that stops an all-green all-claim run from looking like a proof.

### 4.4 Lockstep on the Domino listing — `src/debug/lockstep.rs`, `lockstep_run.rs`

`PairRecord` (`lockstep.rs:394`) hard-codes `equal_output: Verdict` — the conjunction of
`equal-aborts` and `same-output` (`lockstep_run.rs:317`). Under `prove` semantics those two have
**different dependency sets** (`equal-aborts` ← ∅, `same-output` ← `no-abort`), so they cannot
share a verdict. Replace with a per-claim map:

```rust
pub struct ClaimVerdict {
    pub claim: String,
    pub verdict: Verdict,
    /// Sub-verdicts of `invariant`, present only when it is neither verified
    /// nor unreachable. Empty for every other claim.
    pub relations: Vec<RelationVerdict>,
}
pub struct PairRecord { ..., pub claims: Vec<ClaimVerdict> }
```

`equal-output` survives as a **presentation grouping in the EasyCrypt report only**, where the two
claims genuinely do share the empty dependency set. This ripples into `LockstepSummary`,
`VerdictPairCount`, `LockstepRun::is_ok` (`lockstep_run.rs:242`) and the joint-tree viewer's
columns, and it is the largest single piece of work in the story — exposing `ListingKind::Domino`
is not just deleting an `#[allow(dead_code)]`.

`run_lockstep_on` takes the claim set as a parameter. `run_lockstep_command` becomes a thin wrapper
passing the no-dependency set, so `--tactics` is provably unaffected.

### 4.5 `domino easycrypt --debug` — `src/easycrypt/`

Exports first, then sweeps every equivalence proofstep and every exported oracle, narrowing with
`--proofstep` / `--oracle`, exactly as `--check-alignment` and `--tactics` do. Per oracle it calls
`run_lockstep_command` — the same call `tactics/mod.rs:525` makes, with the same hard-coded
options. Exit non-zero if any joint path fails equal-output or invariant.

### 4.6 Output layout

```
_build/debug/domino/<theorem>/<left>-<right>/<oracle>/<claim>/        --claim given
_build/debug/domino/<theorem>/<left>-<right>/<oracle>/!all-claims!/   all-claim run
<out>/<theorem>/!debug!/<left>-<right>/<oracle>/                      easycrypt --debug, --tactics
```

`<out>` is `domino easycrypt --out`, default `_build/easycrypt` — the EasyCrypt debug artifacts sit
beside the export they describe, under the theorem they belong to. The `domino/` segment is new for
the `--claim` case too: one consistent break in a regenerable `_build`, rather than a layout where
a path segment's presence silently encodes a flag.

Both Domino strategies write into the **same** directory and **coexist**, because comparing them on
one oracle is a thing you will want to do. Every collidable artifact carries its strategy — today
both reporters write `trace.json`, `summary.txt`, `index.html`, `inlined.txt`, `models/`, `smt/`
and `transcript.smt2` (`report.rs:24,58,78`; `lockstep_report.rs:63,65,70`):

```
<oracle>/!all-claims!/
    inlined.txt                 shared — identical, both lower the same Domino listing
    sequential_viewer.html   sequential_trace.json   sequential_summary.txt
    lockstep_viewer.html     lockstep_trace.json     lockstep_summary.txt
    sequential/  { smt/, models/, transcript.smt2 }
    lockstep/    { smt/, models/, transcript.smt2 }
```

`_viewer` always means the HTML, `_trace` always means the JSON. A run rewrites only its own
strategy's files; it never wipes the other's.

`DebugRun` gains `strategy: &'static str` (`"sequential"`), matching `LockstepMeta.mode` /
`.listing` (`lockstep_run.rs:157`), and both summary headers name it.

**The EasyCrypt directory keeps `index.html` / `trace.json` / `summary.txt` unchanged.** Only one
strategy ever writes there, so there is nothing to disambiguate, and `live.lockstep_done`
(`tactics/live/mod.rs:342`) keeps resolving `index.html` by relative href with no change. This is
deliberate: the point is that `--tactics` is untouched.

### 4.7 Sweep output

While running: one line per oracle. At the end: a single project-wide table of failures, and
`_build/debug/domino/index.html` + `summary.txt` linking every run. When a single oracle is named,
keep today's concise per-oracle stdout report (story 17) exactly as it is.

Exit code: non-zero if any claim on any pair anywhere is `GoalFails` or `Inconclusive`. Neither
flavour of `Unreachable` is a failure.

### 4.8 Documentation to update

- `00-overview.md` §3: the *Claim scope* and *Assumptions* rows (done by this story).
- `docs/stories/easycrypt/00-overview.md` §2: the `domino debug --easycrypt` row (done).
- `docs/adr/0002-…` §Consequences references `domino debug --easycrypt` (done).
- `CONTEXT.md`: **all-claim run**, **Strategy**, and a scoped **Unreachable** (done).
- `src/debug/lockstep_run.rs` module doc claims *"Domino's abort return carries no game state
  (`smt_construct_abort` ignores it), so on a side that aborts the new state is unconstrained."*
  This is **wrong**: `smt_construct_abort` (`oracle.rs:352`) threads the game state through, and
  the story-23 implementation report says so. Fix the comment.

## 5. Acceptance criteria

- [ ] `domino debug` with no arguments walks every theorem, equivalence proofstep, oracle and
      claim of the project and reports a per-claim verdict for each.
- [ ] `domino debug --claim C --proof T --proofstep N --oracle O` produces the **same verdicts and
      the same solver query count** as before the story (modulo the `domino/` path segment).
- [ ] **Path-condition reuse:** an all-claim run's *exploration* query count — branch pruning plus
      pair vacuity — equals that of a single-claim run over the same base frame. Only the level-3
      goal queries scale with the claim count.
- [ ] **Agreement with `prove`:** for every oracle and claim of `hello-world`,
      `simple-KEM-example`, `test-projects/test-splitinvoke` and the rule oracles, `prove`'s
      per-claim verdict equals "the all-claim run found no `GoalFails` for that claim". A
      `cvc5-lib` differential test.
- [ ] A pair where one side aborts reports `Unreachable { DependencyFalse { "no-abort" } }` for
      `invariant` and `same-output`, and a real verdict for `equal-aborts` — **with no solver call
      spent on deciding it**.
- [ ] `domino debug --lockstep` on the Domino listing reports `equal-aborts` and `same-output` as
      two claims with distinct verdicts, not one `equal-output`.
- [ ] Running sequential and then `--lockstep` on the same oracle leaves both sets of artifacts
      intact and readable, with each summary header naming its strategy.
- [ ] `domino debug --easycrypt` is gone: clap rejects the flag.
- [ ] `domino easycrypt --debug` sweeps every proofstep and oracle, narrows with `--proofstep` /
      `--oracle`, and writes to `<out>/<theorem>/!debug!/…`.
- [ ] **`--tactics` is byte-identical** before and after, on kem-dem: same `Eq_*.ec`, same
      `Eq_*.report.txt`, same accepted-tactic count.
- [ ] `cargo build --workspace --features cvc5-lib` and `cargo test --workspace --features
      cvc5-lib` pass; the default build still works.

## 6. How to verify

```bash
cargo build --workspace --features cvc5-lib

cd example-projects/hello-world
cargo run --features cvc5-lib --bin domino -- debug              # the whole project
cargo run --features cvc5-lib --bin domino -- debug --lockstep

cd ../simple-KEM-example
cargo run --features cvc5-lib --bin domino -- debug --proof <T> --proofstep 0 --oracle Run
cargo run --bin domino -- prove --proof <T> --proofstep 0 --oracle Run   # must agree

cd ../kem-dem/kem-dem-cca-ssp
cargo run --features cvc5-lib --bin domino -- easycrypt --debug --proofstep 0 --oracle PKDEC
```

Weaken `theorem/invariant.smt2` on kem-dem and confirm an all-claim run names *which* claims fail
and on which pairs; restore it and confirm every claim is `verified` or `unreachable`.

> **Never** run any of this against `example-projects/4WHS` or `example-projects/yao` — the slow
> projects in `example-projects/known-good-slow.txt`. See `00-overview.md` §7.

## 7. Notes / risks

- **All-claim runs explore more paths than a narrowed run.** Without `no-abort` in the base frame,
  left abort paths are no longer pruned at the fork; they are enumerated and come back
  `Unreachable { DependencyFalse }` at the terminal pair. This is the price of one shared
  exploration and it is correct — the verdicts are unchanged, only the path count grows. If it
  bites on a large project, `--claim` is the escape hatch, which is exactly why single-claim runs
  keep their base-frame assumptions.
- **Why agreement with `prove` holds.** Paths are exhaustive and disjoint, and moving a dependency
  from the base frame to the terminal pair does not change the conjunction the solver sees there.
  Pruning only changes which pairs get enumerated, and a pruned pair is `unsat` anyway. The
  remaining gap is the per-path DSA encoding vs `prove`'s monolithic oracle functions, which
  story 05's cross-check covers.
- **`Inconclusive` breaks the agreement test.** Keep it to projects where every query decides;
  treat `unknown` on either side as a test failure, not a pass.
- Story 14 (parallel exploration) and story 15 (no oracle functions in the debug frame) are written
  but unimplemented. Neither blocks this story, but 14 becomes more attractive once a sweep is one
  command.
