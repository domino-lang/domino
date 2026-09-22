# Story 16 — `easycryptify`: lowering early exits without duplicating code

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** stories 03 (package modules), 04 (routers). Do **after** story 14, which renamed
the generated theories.
**Blocks:** 08, 09 (both get simpler — see §8), 17.

**This story amends the overview's "Early return / abort mid-body" and "Pipeline" decisions, and
reverses two explicit instructions in story 03 (§3.5 and the first two bullets of §6).** Those said
to keep `treeify`'s shape and not to re-flatten it. That was right when the EasyCrypt writer was
the only consumer and the debugger lowering was hypothetical. It is wrong now, and §1 is the
evidence.

---

## 1. Why this story exists

The export pipeline runs `treeify` (`src/transforms/treeify.rs`), a transform written for the
**SMT** writer. Its contract is "an `if` is the last statement of its block", because the SMT
writer emits a single nested `ite` *term*, and a term has no sequencing — so the continuation of an
`if` has nowhere to go except inside both arms.

EasyCrypt has sequencing. It restricts us to **one exit point**, not to one statement. We are
paying `treeify`'s price for a constraint EasyCrypt does not impose.

### 1.1 What it costs, measured

`Send3` in `example-projects/4WHS/packages/KX_nochecks.pkg.ssp` is 18 lines of Domino:

```
oracle Send3(ctr: Integer, msg: (Bits(n),Bits(n))) -> (Bits(n), Bits(n))
{
    assert not (State[ctr] == None);
    state          <- Unwrap(State[ctr]);
    return         <- invoke Run3(state,msg);
    (state,msg_)   <- parse return;
    (_U,_u,_V,_ltk,_acc,_k,_ni,_nr,_kmac,sid,_mess) <- parse state;
    if (_mess == 2){
        if (First[Unwrap(sid)] == None) {
            First[Unwrap(sid)] <- Some(ctr);
        } else {
            if (Second[Unwrap(sid)] == None) {
                Second[Unwrap(sid)] <- Some(ctr);
            }
        }
    }
    State[ctr] <- Some(state);
    return msg_;
}
```

Its counterpart in `example-projects/4WHS/_build/easycrypt/Full4WHS/Pkg_KX_noprfkey.ec`:

| | today |
|---|---|
| lines | **131** |
| `if` statements | **19** |
| blocks nested at the deepest point | **12** |
| branches with an empty body | **17** |
| copies of the 3-statement tail | **4** |
| `unwrap_N` temporaries | **8** |

The four tail copies are `treeify`: it appended the continuation to every leaf of the
`if (_mess = 2)` cascade. The cost compounds — `k` sequential branch points give up to `2^k` copies
of the final tail, and `treeify` recurses *into* each copy, so any `if` inside the continuation is
duplicated again.

Worse, some of that work is thrown away. `treeify` appends the continuation to branches that have
already aborted too; `translate_block` then discards it (`src/writers/easycrypt/package.rs:739`).
The copy was built, recursed into, and dropped.

### 1.2 What it should look like

`Send1` today — 3 `if`s, 2 of them empty, for a straight-line oracle with no joins at all:

```ec
  proc d_Send1(ctr : int) : bits_n option = {
    ...
    if (!(d_State.[ctr] = None)) {
      if (d_State.[ctr] = None) {

      } else {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run1(state);
        if (ec_r1 = None) {

        } else {
          d_return <- oget ec_r1;
          (state, msg) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg;
        }
      }
    } else {

    }
    return ec_result;
  }
```

After this story:

```ec
  proc d_Send1(ctr : int) : bits_n option = {
    ...
    if (!(d_State.[ctr] = None)) {
      if (!(d_State.[ctr] = None)) {
        unwrap_1 <- oget d_State.[ctr];
        ec_r1 <@ O.d_Run1(state);
        if (!(ec_r1 = None)) {
          d_return <- oget ec_r1;
          (state, msg) <- d_return;
          d_State.[ctr] <- state;
          ec_result <- Some msg;
        }
      }
    }
    return ec_result;
  }
```

Same three `if`s — one per abort point in the source, which is the honest number — but no empty
branches, no dead `else`, half the lines. (The duplicated `d_State.[ctr] = None` test is story 17.)

## 2. Inherited context — read this before touching anything

Every story here is self-contained because the implementation session starts with a fresh context.

### 2.1 The statement AST (`src/statement.rs`)

```rust
pub struct CodeBlock(pub Vec<Statement>);

pub enum Statement {
    Abort(SourceSpan),
    Return(Option<Expression>, SourceSpan),
    Assignment(Assignment, SourceSpan),
    InvokeOracle(InvokeOracle),          // bare invoke, return value discarded
    IfThenElse(IfThenElse),
    For(Identifier, Expression, Expression, CodeBlock, SourceSpan),
}

pub enum AssignmentRhs {
    Expression(Expression),
    Sample { ty, sample_name, sample_id },
    Invoke { oracle_name, args, edge, return_type },
}

pub enum Pattern { Ident(Identifier), Table { ident, index }, Tuple(Vec<Identifier>) }

pub struct IfThenElse { cond, then_block, else_block, then_span, else_span, full_span }
```

### 2.2 Three shapes the parser and earlier transforms have already fixed

- **`assert c` is not a statement kind.** The parser desugars it (`src/parser/package.rs:1275`) to
  `IfThenElse { cond: c, then_block: [], else_block: [Abort], .. }` — note the *empty then-block*.
  This story needs no special case for `assert`; the generic rule in §3.3 catches it.
- **`Unwrap` is not desugared into a branch by anyone.** `unwrapify`
  (`src/transforms/unwrapify.rs:66`) only hoists each `Unwrap(e)` sub-expression out into its own
  statement `unwrap-N <- Unwrap(e)` (`Identifier::Generated`, per-oracle counter, 1-indexed). It
  stays an ordinary assignment. The branch is invented later and separately by the debug IR
  (`InlStmt::Unwrap`) and by the EasyCrypt writer (story 03 §3.5). **This story invents it once,
  in the transform, and both consumers stop inventing it.**
- **`returnify` has run**, so every path through an oracle body ends in a `Return` or an `Abort`.
- **`loopunroll` has run**, so a surviving `For` is an unbounded loop with no EasyCrypt
  translation — a hard error, as today.

### 2.3 The pipeline (`src/transforms/theorem_transforms.rs`)

`transform_game_inst_common(game_inst, run_treeify: bool)` is shared by `EquivalenceTransform`
(`true`, feeds the SMT writer) and `DebugTransform` (`false`, feeds `inline_oracle` and the
symbolic executor). Order: `type_extract`, `deconstructinvoke`, `unwrapify`, `resolveoracles`,
`samplify`, `loopunroll`, `sample_max_counter_extractor`, `returnify`, *[treeify]*,
`tableinitialize`.

`src/writers/easycrypt/export.rs:164` runs `EquivalenceTransform` itself, so callers hand it an
untransformed `Theorem`.

### 2.4 Facts about Domino compositions this story relies on

Confirmed by the project owner:

- The composition graph is a **DAG** — no cycles.
- An oracle **cannot call another oracle of its own package**.
- Packages **do not share state**. (The SMT encoding puts all game state in one datatype, but that
  is an encoding detail, not shared ownership.)

Together: an `invoke` can only write the *callee's* state, never the caller's. Story 17 depends on
this; this story only needs it to know that an `invoke` cannot invalidate anything about the
caller's own control flow.

### 2.5 What the writer does today (story 03 §3.3–3.5) — all of it is going away

`translate_block` (`src/writers/easycrypt/package.rs:739`) currently:

- returns early on `Abort`, discarding the rest of the block;
- returns early on `Return`, emitting `ec_result <- Some …` first;
- on `Unwrap` and on `Invoke`, builds an `if (e = None) { } else { …; <rest of block> }` and
  recurses the *remainder of the block* into the `else` — the "continuation nesting" of story 03
  §3.5;
- synthesises the `ec_result` local and the trailing `return ec_result;`;
- names invoke temporaries `ec_r<N>` via `declare_temp`.

## 3. The algorithm

`easycryptify` is a Domino→Domino transform. **Its output is ordinary, valid, typecheckable Domino
with the same observable behaviour as its input.** That property is what makes it testable (§5) and
what makes `domino debug --easycrypt` meaningful.

Put a new file at `src/transforms/easycryptify.rs`, following the shape of the other transforms
(`pub struct Transformation<'a>(pub &'a Composition)` implementing `super::Transformation`).

### 3.1 The contract

After `easycryptify`, every oracle body satisfies:

1. It contains **no `Abort`**, and exactly **one `Return`**, as its final statement.
2. That `Return` returns the local `ec_result`.
3. The oracle's signature return type is `Maybe(T)` where it was `T`.

That is EasyCrypt's single-exit rule, expressed in Domino. The writer then lowers statement by
statement with no control-flow reasoning of its own.

### 3.2 Terminality

The one piece of analysis. For a statement, "can this terminate the oracle?"

```rust
enum Term { Never, Maybe, Always }
```

| statement | `Term` |
|---|---|
| `Abort`, `Return` | `Always` |
| `Assignment` whose rhs is `Expression(Unwrap(_))` | `Maybe` |
| `Assignment` whose rhs is `Invoke { .. }`, and bare `InvokeOracle` | `Maybe` |
| `Assignment` with any other rhs (including `Sample`) | `Never` |
| `IfThenElse` | `Always` if both branches are `Always`; `Never` if both are `Never`; else `Maybe` |
| `For` | hard error — see §3.6 |

For a **block**: fold left to right. The first `Always` makes the block `Always` (anything after it
is unreachable). Otherwise `Maybe` if any statement is `Maybe`, else `Never`.

`Term` is computed on the **input** statements, before lowering.

### 3.3 The lowering

```rust
/// Lowers one block. `stmts` is the block; the returned statements never
/// terminate early. The bool is true if any path through them can set `ec_done`.
fn lower(&mut self, stmts: &[Statement]) -> (Vec<Statement>, bool)
```

Walk `i` from `0`; let `S = stmts[i]` and `REST = &stmts[i+1..]`.

**`Abort`** — emit `ec_done <- true`. `REST` is unreachable; drop it. Return `(out, true)`.

**`Return(v)`** — emit `ec_result <- Some(v)` (for a valueless return, `Some(())` —
`ExpressionKind::Bot` is the `()` value, `src/types.rs:214`) then `ec_done <- true`. Drop `REST`.
Return `(out, true)`.

**`Assignment(x, Unwrap(e))`** — emit

```
if (not (e == None)) {
    x <- Unwrap(e)          // cannot abort here any more; the writer emits `oget e`
    <lower(REST)>
} else {
    ec_done <- true
}
```

and return `(out, true)`. `REST` is consumed.

**`Assignment(x, Invoke{..})` and bare `InvokeOracle`** — the callee now returns `Maybe(T)` (§3.4),
so bind a temporary and check it:

```
ec_rN <- invoke O(args)     // ec_rN : Maybe(T), Identifier::Generated("ec_rN", …)
if (not (ec_rN == None)) {
    x <- Unwrap(ec_rN)      // omitted for a bare InvokeOracle
    <lower(REST)>
} else {
    ec_done <- true
}
```

Number `ec_rN` per oracle, starting at 1, to keep the goldens close to today's. Return
`(out, true)`. `REST` is consumed.

**`IfThenElse { cond, then_block, else_block }`** — four cases on
`(Term(then_block), Term(else_block))`:

- **`(Always, Always)`** — emit `if cond { lower(then) } else { lower(else) }`. `REST` is
  unreachable; drop it. Return `(out, true)`.
- **`(Always, _)`** — the `else` branch is the only survivor, so the continuation belongs to it:
  emit `if cond { lower(then) } else { lower(else ++ REST) }`. Return; `REST` is consumed.
- **`(_, Always)`** — symmetric: `if cond { lower(then ++ REST) } else { lower(else) }`. **This is
  the `assert` case** — `else_block` is `[Abort]`, which is `Always` — and it is what turns
  `assert c; REST` into `if (c) { REST } else { ec_done <- true }` with one branch and no empty
  block.
- **neither is `Always`** — lower each branch independently:

  ```
  let (then', d1) = lower(then_block);
  let (else', d2) = lower(else_block);
  emit if cond { then' } else { else' };
  ```

  - if `d1 || d2`, this `if` is a **join of two live paths**, which is the one shape that genuinely
    needs the flag: emit `if (not ec_done) { <lower(REST)> }` and return `(out, true)`.
  - otherwise nothing under it can abort: **continue the loop at `i+1`**, leaving `REST` exactly
    where the Domino source had it. No guard, no nesting, no duplication.

**Anything else** (plain assignment, sample) — emit it unchanged and continue at `i+1`.

Three properties worth stating explicitly, because they are what make this correct:

- **No statement is ever duplicated.** `REST` is moved, never copied.
- **No abort ever moves.** Every guard sits exactly where the statement that could abort sat, so a
  state write that happened before an abort still happens, and one that happened after still does
  not. (Domino keeps writes made before an abort; so does the generated EasyCrypt.)
- **The flag appears only at a real join.** In `Send3` that is once, after the `if (_mess = 2)`
  cascade.

### 3.4 Wrapping up the oracle

For each oracle:

1. Prepend `ec_result <- None` and `ec_done <- false`.
2. Body is `lower(oracle.code)`.
3. Append `return ec_result`.
4. Rewrite the signature's return type `T` → `Maybe(T)`.

`ec_result` is `Identifier::Generated("ec_result", Maybe(T))`, `ec_done` is
`Identifier::Generated("ec_done", Type::boolean())`. Both mangle to themselves (lowercase-first
survives, overview §3 "Naming").

An oracle already returning `Maybe(T)` becomes `Maybe(Maybe(T))` → `T option option` in EasyCrypt.
That is correct and necessary: the outer option is abort, the inner is the value. **No project
under `example-projects/` or `test-projects/` has a `Maybe`-returning oracle**, so this needs a
hand-written unit test, not a golden.

**Signatures travel.** `OracleSig` appears in `Composition.edges`, `Composition.exports` and
`split_exports` as well as on the `OracleDef`. Rewrite all of them together, or a caller's
`if (ec_rN == None)` check will disagree with its callee's declared type and the output will not
typecheck as Domino.

**Drop `ec_done` when it is not needed.** After lowering an oracle, if its body contains no
`if (not ec_done)` guard, delete every `ec_done` assignment and its declaration. The `else`
branches that held them become empty, and the writer omits an empty `else` entirely (§3.5) — which
is what produces the `Send1` shape in §1.2. Most oracles land here.

### 3.5 What the writer loses

In `src/writers/easycrypt/package.rs`:

- `translate_block` drops the `Unwrap` and `Invoke` continuation-nesting (story 03 §3.5), the
  early-return-and-discard behaviour for `Return`/`Abort`, `declare_temp`, and the synthesised
  `ec_result`. `Abort` becomes `unreachable!()`. `Return(Some(e))` becomes `return <e>;`.
  `IfThenElse` emits both blocks and **passes `else_block: None` when the else block is empty** —
  the AST and renderer already support this (`ast.rs:131` is `Option<EcBlock>`, `render.rs:309`
  skips it); the writer simply never passes `None` today.
- The option-wrapping comes off, because `translate_type` already maps `Maybe(T)` to `T option`
  (`types.rs:50`) and the signatures are now `Maybe`-typed. Six sites double-wrap if left alone:
  `interfaces.rs:104`, `package.rs:401`, `package.rs:640`, `package.rs:996`, `game.rs:221`,
  `game.rs:417`. (The `EcType::Option` uses in `invariant.rs` are SMT sort translation and are
  unrelated — leave them.)

`ec_result` and `ec_r<N>` now arrive as ordinary Domino locals, so `collect_locals`
(`package.rs:650`) picks them up with no change. Check that the declaration order it produces still
puts `ec_result` first; if not, that is a cosmetic golden churn, not a bug.

### 3.6 Pipeline wiring

Add `EasyCryptTransform` to `src/transforms/theorem_transforms.rs`. `transform_game_inst_common`'s
`run_treeify: bool` becomes a three-way enum (`Treeify` / `None` / `EasyCryptify`) — the file's own
comment says the variants "must never drift, so the only difference between them lives here", and
that stays true with three.

`easycryptify` runs **last, after `tableinitialize`** — not in `treeify`'s slot. `tableinitialize`
pattern-matches on `T[k] <- invoke …` (`tableinitialize.rs:57`), a shape this transform rewrites,
so it has to see the code first.

Switch `export.rs:164` to `EasyCryptTransform`. That is the only call site to switch in this story.

**The debugger is not wired here, because there is nothing to wire yet.** `--easycrypt` does not
exist as a CLI flag, and `src/debug/driver.rs:544` uses `DebugTransform` unconditionally. What this
story does owe the debugger is two things:

- Update the comment block at `src/debug/driver.rs:529` — it explains why *two* transforms of the
  same theorem exist and now has to name the third, so the next reader does not assume
  `EasyCryptTransform` was an oversight.
- Leave `DebugTransform` **completely untouched**. Plain `domino debug` / `domino inline` must keep
  running `treeify`-free Domino, where an `assert` still has the empty `then_block` and `[Abort]`
  else that `ir.rs:563` matches on. See §6.

Stories 08 and 09, when they add `--easycrypt`, must select `EasyCryptTransform` for that flag and
`DebugTransform` without it — recorded in §8.

`treeify` itself is **not touched**. It keeps serving the SMT writer through
`EquivalenceTransform`, and its tests keep passing.

A `For` that reaches `easycryptify` is the same hard error the writer raises today
(`EcExportError::UnsupportedStatement`), just raised earlier. Keep the span.

## 4. Acceptance criteria

- [ ] New `src/transforms/easycryptify.rs`; `treeify.rs` unmodified; `DebugTransform` unmodified.
- [ ] A plain `domino inline` (no `--easycrypt`) on an oracle containing an `assert` still renders
      `assert (…);` in its listing — regression test, because this is the one thing the owner
      explicitly does not want changed.
- [ ] Every exported oracle body contains no `Abort`, exactly one `Return`, as its last statement.
- [ ] `Send1` in `Pkg_KX_noprfkey.ec` matches §1.2 — 3 `if`s, **no empty branches**, no `else` on
      an abort-only branch.
- [ ] `Send3` in `Pkg_KX_noprfkey.ec`: the 3-statement tail appears **once**, and exactly **one**
      `if (!ec_done)` guard exists in the oracle. Record the new line/`if`/depth counts against the
      table in §1.1.
- [ ] An oracle with no join (e.g. `NewSession`) declares **no `ec_done` at all**.
- [ ] An oracle with no return value produces `: unit option` and `Some tt`, as before.
- [ ] An oracle already returning `Maybe(T)` produces `T option option` — hand-written unit test.
- [ ] Unit tests on `CodeBlock` in/`CodeBlock` out, no solver, in the default suite: each of the
      four `IfThenElse` cases of §3.3; `assert` (must produce one `if`, continuation inside, no
      empty then-block); unwrap; invoke; nested `if` under an `if`; an oracle where nothing can
      abort (output must be statement-for-statement the input plus the wrapper).
- [ ] Idempotence is **not** required (the output has no `Abort` left to lower), but running the
      transform twice must not panic. Assert that.
- [ ] `cargo test --workspace easycrypt` green; goldens under `testdata/easycrypt/` regenerated and
      reviewed by eye, not just accepted.
- [ ] Every generated `.ec` still compiles under `easycrypt compile` (`assert_compiles_or_known_base_case_gap`).
- [ ] `cargo build/test/clippy --workspace` clean; output deterministic.

## 5. How to verify

```bash
cargo test --workspace easycrypt
cargo test --workspace easycryptify
cargo test --workspace -- --ignored easycryptify_matches_treeify   # the solver test, §5.1
```

### 5.1 The differential test

Unit tests cover shape; this covers **meaning**. Because `easycryptify`'s output is still runnable
Domino, both versions of an oracle can be symbolically executed with the machinery already in
`src/debug/` and compared by cvc5.

For one oracle, build it twice — once through `EquivalenceTransform` (treeified, the trusted
reference) and once through `EasyCryptTransform` — then assert with cvc5 that for **equal
arguments, equal prior state and equal randomness** the two cannot disagree, where "agree" is:

- the treeified oracle aborts **iff** the easycryptified one returns `None`; and
- the treeified oracle returns `v` **iff** the easycryptified one returns `Some(v)`; and
- the resulting package state is identical.

Use the per-path SMT the executor builds (`src/debug/exec.rs`) — a flat, acyclic, single-assignment
conjunction. **Do not** compare `PathEffect`s from `src/debug/effect.rs`: its own header says it is
"human-facing and deliberately lossy … never fed to the solver and no verdict depends on it", so a
passing comparison there would prove nothing.

Oracle list, and why each is on it:

| oracle | what it proves |
|---|---|
| `KX_nochecks::Send3` | the 4-live-leaf cascade — the flag, and the tail collapsing to one copy |
| `KX::Send2` | nested unwraps under an invoke |
| `KX::NewSession` | no join; proves the flag is **absent** when it is not needed |
| any all-paths-abort oracle | the `(Always, Always)` case and the dropped continuation |

Mark it `#[ignore]` and run it in CI. It needs cvc5 and runs a symbolic execution twice per oracle,
so it must stay out of `cargo test`'s hot path; the `CodeBlock`-level unit tests are the ones that
run while developing.

## 6. Notes / risks

- **The `--easycrypt` listing loses `assert`; the Domino listing must not.** The debug IR detects
  an assert *structurally* — `ir.rs:563`, `then_block.0.is_empty() && else_block == [Abort]`. §3.3
  fills that then-block, so easycryptified code renders `if (...) {` instead of `assert (...);`,
  and the executor's decision labels change from "guard held / failed" to "taken / not taken"
  (`exec.rs:787`).

  **This is intended for `--easycrypt` only.** That view exists to show a user the EasyCrypt they
  have to prove things about, and EasyCrypt has no `assert`. **Plain `domino debug` and
  `domino inline` on Domino code must keep showing `assert`**, and they do, because they run
  `DebugTransform` (`driver.rs:544`), which this story does not touch and which never runs
  `easycryptify`. The two views differ on purpose and by construction — the transform, not a flag
  inside the IR, is what makes them differ.

  Two ways an implementer could break this, both forbidden: running `easycryptify` in
  `DebugTransform`, and "fixing" `ir.rs:563` to keep matching easycryptified code. If a test ever
  shows `assert` disappearing from a plain Domino listing, that is a bug in this story.
- **`ec_done` is dead code in Domino and load-bearing in EasyCrypt.** In Domino the `Return`/`Abort`
  it replaces would have terminated, so a guarded continuation is simply skipped and the flag is
  never observably read. In EasyCrypt, where control falls through, the flag is the whole mechanism.
  This is exactly why the §5.1 differential test is sound: it checks the Domino semantics the
  transform preserves, and the writer's remaining job is a near-identity lowering.
- **Do not reintroduce the empty `then` branch.** Story 03 §6 said to keep it so the debugger could
  point at the abort line. Story 08 is unimplemented and now inherits a shape where the abort is
  the `else` of a named guard, which is at least as pointable-at. Story 03 §6 is superseded here.
- **Watch the `(Always, _)` case.** It is the rarer mirror of the assert case and easy to get
  backwards. The continuation goes into the branch that does **not** always terminate.
- **Signature rewriting is the likeliest source of a confusing failure.** If `edges`/`exports` are
  missed, the symptom is a router or caller that typechecks in Rust and produces `T option option`
  or a type error in EasyCrypt, far from the cause.

## 7. Deferred — recorded here on purpose, do not do them in this story

These were reviewed with the owner and explicitly postponed. They are cleanups on *guards*, not on
control flow, and none of them is needed for the numbers in §1.1.

1. **Merging adjacent guards** — `if c1 { if c2 { X } }` → `if (c1 /\ c2) { X }`, collapsing the
   consecutive `ni`/`nr` unwrap guards into one branch. Safe only when the second condition reads
   nothing the first guard's body bound and no state write sits between.
2. **Redundant-condition elimination** — dropping a test already implied by a dominating one. This
   is what would kill the duplicated `d_State.[ctr] = None` in §1.2 (the `assert` and the `Unwrap`
   test the same thing). Story 17 builds the dominating-guard analysis this needs, so it becomes
   cheap afterwards — but it is still out of scope there unless the owner asks.
3. **Table-index disequality** — refining write-invalidation with `k ≠ k'` reasoning instead of
   invalidating all reads of a table.

Story 17 covers the fourth item, `unwrap_N` temporaries, on its own.

## 8. State handed to the next story

Record in `16-easycryptify-IMPLEMENTATION-REPORT.md`:

- the measured `Send3` and `Send1` numbers after the change, against §1.1's table;
- the exact `Term` rules as implemented, if any case was refined;
- the `ec_done`/`ec_result`/`ec_r<N>` naming and the "drop `ec_done` when unused" rule as
  implemented;
- which oracles ended up with a flag across all example projects — if it is more than a handful,
  say so, because it means §3.3's last case is firing more than expected;
- the golden paths that moved.

**For stories 08 and 09 — the transform is selected by the flag.** `--easycrypt` uses
`EasyCryptTransform`; without it, `DebugTransform`, unchanged. That is what keeps `assert` rendering
as `assert` in the Domino listing while the EasyCrypt listing shows the `if` that EasyCrypt actually
has. Do not try to reconcile the two listings.

**For stories 08 and 09:** the easycryptified Domino is now nearly 1:1 with the emitted EasyCrypt —
one `if` per source abort point, no duplication, a single exit. The EC-AST→IR lowering they specify
has correspondingly less to reconcile, and the 1:1 statement↔label relationship that `DebugTransform`
skips `treeify` to preserve now holds for the EasyCrypt listing too. Neither story's text is
rewritten here; read this section before starting either.

**For story 17:** the guard for each `Unwrap(e)` now sits at exactly the point `unwrapify` put the
binding, which is the invariant story 17's analysis rests on.
