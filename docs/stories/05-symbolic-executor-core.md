# Story 05 — Symbolic executor core (no solver)

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 02 (`DebugTransform`, `src/debug/ir.rs`).
**Blocks:** story 06.

---

## 1. Why this story exists

This is the heart of the epic: turning one inlined oracle into a set of **execution paths**, each
carrying its own flat SMT encoding. Deliberately **no solver is involved** — the executor
enumerates every syntactic path and hands back the SMT for each. That makes it unit-testable on
its own, and it is exactly what the debugger needs for the left side in its default (cheap) mode.
Story 06 adds solver-guided pruning on top without changing this code.

The output replaces, per path, the single monolithic constraint the prover uses:

```smt2
; prove:
(assert (= <return-Left-…> (<oracle-Left-…> <old-state-Left> <consts> <args…>)))

; debug, one path:
(declare-const |<v!left!7!dk>| Bits(dkeyl)) (assert (= |<v!left!7!dk>| ...))
...
(assert <path condition 1>) (assert <path condition 2>) ...
(assert (= <return-Left-…> (mk-return-… <reconstructed game state> (mk-return-value-… <expr>))))
```

## 2. Inherited from earlier stories

From **story 02** (`src/debug/ir.rs`):

```rust
pub type Label = usize;         // 1-based line number in InlinedOracle::listing.text
pub type VarKey = String;       // "{pkg_inst}#{frame_id}::{name}"

pub struct InlinedOracle { game_inst_name, oracle_name, entry_pkg_inst, args, return_type,
                           body: InlBlock, listing: Listing }
pub struct InlBlock(pub Vec<InlStmt>);
pub enum InlStmt {
    Assign { label, target: Place, rhs: Expression },
    Sample { label, target: Place, sample_id: usize, ty: Type, sample_name: String },
    Unwrap { label, target: Place, inner: Expression },
    Branch { label, cond: Expression, then: InlBlock, els: InlBlock, is_assert: bool },
    Call   { label, frame: FrameInfo, bind: Option<Place>, body: InlBlock },
    Return { label, value: Option<Expression> },
    Abort  { label },
}
pub enum Place { Local { key: VarKey, ty }, State { pkg_inst, field, ty },
                 Index { base, index }, Discard }
pub struct FrameInfo { frame_id, pkg_inst_name, oracle_name, arg_bindings, return_type }
```

Key semantics established there:

- **Locals** are already alpha-renamed per frame — two frames never collide.
- **Package state** is *not* frame-scoped; it is keyed `(pkg_inst, field)` globally. This is what
  reproduces the prover's "write locals back before an invoke" behaviour for re-entrant calls.
- **`Call` bodies are nested.** A `Return` inside a frame means "bind `frame.bind`, pop the frame,
  continue after the `Call`". A `Return` at depth 0 is a terminal.
- **`Abort` is always a global terminal**, however deep the frame — matching
  `src/writers/smt/writer.rs:771`.

From **story 04** (if it landed first; otherwise just write against the contract):
`emit_constant_declarations(Some(oracle))` leaves `<return-…>` *declared but unconstrained*,
which is the slot this story's terminal encoding fills.

## 3. Existing code this story must mirror

Read these before writing anything — the executor must produce SMT that is *semantically
identical* to what the writer produces, or the debugger will disagree with the prover.

| Concern | Reference |
|---|---|
| plain assignment, table store, unwrap-to-abort | `src/writers/smt/writer.rs:863` (`smt_build_assign`) |
| sampling and counter increment | `src/writers/smt/writer.rs:682` (`smt_build_sample`) |
| invoke: write-back, abort propagation, result binding | `src/writers/smt/writer.rs:771` (`smt_build_invoke`) |
| tuple destructuring (`el{n}-{i}` accessors) | `src/writers/smt/writer.rs:741` (`smt_build_parse`) |
| building a `return` value | `OracleContext::smt_construct_return`, `src/writers/smt/contexts/oracle.rs:181` |
| building an `abort` | `GenericOracleContext::smt_construct_abort`, `src/writers/smt/contexts/oracle.rs:352` |
| writing locals back into the game state | `OracleContext::smt_write_back_state`, `src/writers/smt/contexts/oracle.rs:301` |
| updating one package's state inside the game state | `GameInstanceContext::smt_update_gamestate_pkgstate`, `src/writers/smt/contexts/game_inst.rs:141` |
| building a package state value from fields | `PackageInstanceContext::smt_update_pkgstate_from_locals`, `src/writers/smt/contexts/pkg_inst.rs:198` |
| reading / incrementing a randomness counter | `GameInstanceContext::smt_access_gamestate_rand` (line 123), `smt_increment_gamestate_rand` (line 194) |
| the `__sample-rand-<game-inst>-<sort>` function name | `names::fn_sample_rand_name`, and `smt_composition_randomness` at `src/writers/smt/writer.rs:1135` |
| expression substitution | `Expression::map` (`src/expressions.rs:90`), `Expression::mapfold` (line 228) |
| SMT term construction helpers | `src/writers/smt/exprs.rs`: `SmtExpr`, `SmtLet`, `SmtIte`, `SmtEq2`, `SmtNot`, `SmtAnd`, `SmtAssert`, `SmtAs` |
| declaring a constant | `crate::writers::smt::declare::declare_const(name, Sort)` |

Also relevant: `SampleInfo { tys, count, positions: Vec<Position> }` and
`Position { game_name, inst_name, pkg_name, oracle_name, dst_name, dst_index, sample_id, ty,
sample_name }` in `src/transforms/samplify.rs:16`. `SmtExpr: From<&Position>` renders a
`(sample-id "inst" "oracle" "sample-name")` term.

## 4. Work to do — `src/debug/exec.rs`

### 4.1 Types

```rust
/// Which game instance we are executing. Only used to namespace SSA names and pick sample_info.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Side { Left, Right }

/// One decision taken at a branching point.
pub struct Step { pub label: Label, pub decision: Decision }

pub enum Decision {
    Then, Else,          // Branch { is_assert: false }
    AssertHolds, AssertFails,   // Branch { is_assert: true }
    UnwrapSome, UnwrapNone,     // Unwrap
}

pub enum Terminal { Return { label: Label, value: Option<Expression> }, Abort { label: Label } }

/// A complete path from oracle entry to a terminal, with its SMT.
pub struct TerminalPath {
    pub id: String,               // "L3" or "L3.R2" — assigned by the driver, not here
    pub steps: Vec<Step>,
    /// `declare-const` for every SSA variable introduced on this path, in order.
    pub decls: Vec<SmtExpr>,
    /// Definitional `(assert (= <ssa> <rhs>))` and path conditions, in order.
    pub constraints: Vec<SmtExpr>,
    /// `(assert (= <return-const> <constructed return/abort>))`.
    pub return_constraint: SmtExpr,
    pub terminal: Terminal,
}
```

### 4.2 Executor state

```rust
struct SymState {
    locals:    HashMap<VarKey, SmtExpr>,
    pkg_state: HashMap<(String /*pkg_inst*/, String /*field*/), SmtExpr>,
    rand_ctr:  HashMap<usize /*sample_id*/, usize>,
    steps:       Vec<Step>,
    decls:       Vec<SmtExpr>,
    constraints: Vec<SmtExpr>,
    ssa: usize,
}
```

**Initialisation.**

- `pkg_state[(inst, field)]` starts as the field read out of the *old* game state constant:
  `gctx.smt_access_gamestate_pkgstate(<old-state-const>, inst)` then
  `pctx.smt_access_pkgstate(that, field)`. The old-state constant name comes from
  `gctx.oracle_arg_game_state_pattern().old_global_const_name(game_inst_name)`.
- `rand_ctr[sample_id]` starts at `0` for every sample id. Note
  `emit_constant_declarations` already asserts the old counters are zero
  (`build_rands`'s third element, `src/writers/smt/contexts/equivalence/emit.rs:1472`), and the
  randomness-mapping encoding depends on that — so counting from 0 is correct, not an
  approximation.
- The exported oracle's arguments start bound to the argument constants
  `octx.smt_arg_name(arg_name)` (`src/writers/smt/contexts/oracle.rs:167`), which
  `emit_constant_declarations` already declares and equates across the two sides.

### 4.3 Dynamic single assignment

Every `Assign`, `Sample` and `Unwrap` introduces a fresh constant:

```
name  = format!("<v!{side}!{n}!{basename}>")     // n = state.ssa, then ssa += 1
decls.push(declare_const(name, ty.into()));
constraints.push(SmtAssert(SmtEq2 { lhs: name, rhs: <rhs term> }).into());
```

and then rebinds the store slot (`locals[key] = name` or `pkg_state[(inst, field)] = name`).

`<rhs term>` is the RHS `Expression` with every identifier replaced by its current store value,
converted to `SmtExpr`. Implement the substitution with `Expression::map`:

- an identifier that is a frame-local → `locals[key]`
- an identifier that is a package state field → `pkg_state[(inst, field)]`
- everything else (constants, theorem params, literals, operators) → left alone, so it converts
  exactly as the prover's `From<&Expression> for SmtExpr` would.

**Table writes.** `Place::Index { base, index }` becomes
`("store", <current value of base>, <index term>, <value term>)`, exactly as
`smt_build_assign` does at `src/writers/smt/writer.rs:883`. The fresh SSA constant is then bound
to that whole `store` term and rebound to `base`.

**Discard.** `Place::Discard` (the `_` identifier) introduces no constant and no constraint —
match the `filter(|(x, _)| x != "_")` behaviour in `smt_build_sample`.

**Sampling.** Mirror `smt_build_sample`:

```
ctr      = rand_ctr[sample_id]
rand_val = (<names::fn_sample_rand_name(game_inst_name, ty)> <SmtExpr::from(&position)> ctr)
rand_ctr[sample_id] = ctr + 1
```

where `position = &sample_info.positions[sample_id]`. Note the executor tracks the counter as a
plain `usize` because it starts at 0 and only ever increments — no need to thread it through the
game state term during execution. It is materialised into the reconstructed game state at the
terminal (see 4.5).

### 4.4 Forking

- **`Branch { cond, then, els, is_assert }`** → two children.
  - then-child: `constraints.push(SmtAssert(<cond term>))`,
    `steps.push(Step { label, decision: Then | AssertHolds })`, execute `then` then the
    continuation.
  - else-child: `constraints.push(SmtAssert(SmtNot(<cond term>)))`,
    `decision: Else | AssertFails`, execute `els` then the continuation.
- **`Unwrap { target, inner }`** → two children, mirroring `src/writers/smt/writer.rs:899`:
  - none-child: `constraints.push(SmtAssert(SmtEq2 { lhs: <inner term>, rhs: SmtAs { term: "mk-none", sort: Type::maybe(ty).into() } }))`,
    `decision: UnwrapNone`, and the path **terminates in `Abort`** at this label.
  - some-child: `constraints.push(SmtAssert(SmtNot(<that equality>)))`, bind
    `target` to a fresh SSA constant constrained to `("maybe-get", <inner term>)`,
    `decision: UnwrapSome`, continue.
- **`Call { frame, bind, body }`** → push a frame. Bind each of `frame.arg_bindings` as a normal
  assignment (fresh SSA constant per parameter, RHS substituted in the *caller's* namespace
  before the frame is pushed). Execute `body`. A `Return { value }` inside the frame binds
  `frame.bind` to the substituted `value` (again a fresh SSA constant), pops the frame, and
  continues with the statements after the `Call`.
- **`Return` at depth 0** and **`Abort` at any depth** are terminals.

Implement the walk with an explicit worklist/continuation rather than deep recursion, or with
recursion plus an explicit continuation stack — either is fine, but a `Vec<(&InlBlock, usize)>`
"instruction pointer stack" makes "continue after the `Call`" trivial and keeps stack depth
bounded.

### 4.5 Terminal encoding

At a terminal, produce the missing `<return-…>` constraint that story 04 made room for.

1. **Reconstruct each package instance's state** from `pkg_state`: call
   `pctx.pkg_state_pattern().call_constructor(...)` with the current store value per field —
   i.e. the same shape as `smt_update_pkgstate_from_locals`
   (`src/writers/smt/contexts/pkg_inst.rs:198`) but reading from our store instead of from
   identifier names. Factor a helper rather than duplicating the pattern plumbing.
2. **Fold those into the game state**, starting from the old-state constant, with one
   `gctx.smt_update_gamestate_pkgstate(acc, sample_info, pkg_inst_name, pkg_state_term)` per
   package instance.
3. **Materialise the randomness counters**: for each `sample_id` whose `rand_ctr` is non-zero,
   apply `gctx.smt_update_gamestate_rand(...)` (or `smt_increment_gamestate_rand` `n` times) so
   the final game state carries the advanced counters. This matters — the invariants and the
   randomness-mapping condition read them.
4. Build the return term:
   - `Terminal::Return { value }` → `octx.smt_construct_return(<game state term>, <value term or "mk-empty">)`
   - `Terminal::Abort` → `octx.smt_construct_abort(<game state term>)`
5. `return_constraint = SmtAssert(SmtEq2 { lhs: <return-const name>, rhs: <that term> })`.

The `<return-const name>` is `patterns::ReturnConst { .. }.name()` for the exported oracle of
that game instance — the same constant `build_returns` declares
(`src/writers/smt/contexts/equivalence/emit.rs:1346`).

### 4.6 Entry point

```rust
pub fn execute(
    inlined:   &InlinedOracle,
    game_inst: &GameInstance,       // post-DebugTransform
    sample_info: &SampleInfo,
    side: Side,
    max_paths: Option<usize>,
) -> Result<Vec<TerminalPath>, ExecError>;
```

`ExecError::MaxPathsExceeded { explored, limit }` when the cap is hit — the driver reports how
far it got rather than silently truncating.

Also expose a *streaming* variant (a callback or an iterator) — story 06 wants to interleave
solver queries with exploration rather than materialise every path first:

```rust
pub fn execute_streaming(..., on_path: &mut dyn FnMut(&TerminalPath) -> ControlFlow<()>) -> ...
```

Design this now; story 06 will lean on it.

## 5. Acceptance criteria

- [ ] `src/debug/exec.rs` exposes `Side`, `Step`, `Decision`, `Terminal`, `TerminalPath`,
      `execute`, `execute_streaming`, `ExecError`.
- [ ] Path count matches hand-enumeration on a small oracle: a body with one `if` and one
      `assert` yields 4 paths (then/else × holds/fails), of which the two `assert-fails` ones
      terminate in `Abort`.
- [ ] No SSA constant name is ever reused within a path (assert over `decls`).
- [ ] An `Unwrap` produces exactly two children, and the `UnwrapNone` child's terminal is
      `Terminal::Abort` at the unwrap's own label.
- [ ] A `Call` whose callee returns from inside a branch produces paths that **continue after the
      call** (test on `test-projects/test-splitinvoke`), and the continuation is *not* duplicated
      into the IR.
- [ ] An `Abort` inside a callee frame terminates the whole path.
- [ ] Golden test: for one two-branch oracle, the emitted `decls + constraints +
      return_constraint` of each path is pinned as a string.
- [ ] Consistency test (the important one): for a small oracle, `(and <path conditions>)` implies
      `<return-const> = <oracle-fn applied to the old state>`. You can check this cheaply without
      the new backend by writing the base declarations plus one path to a file and running the
      system `cvc5` on it via `std::process::Command` in an `#[ignore]`d test, or by deferring
      the check to story 06's cross-check. Write down which you did.
- [ ] `cargo build --workspace && cargo test --workspace` pass.

## 6. How to verify

```bash
cargo build --workspace
cargo test  --workspace
cargo test  --workspace -- --nocapture debug::exec
```

Projects to test against, smallest first:

1. `test-projects/test-loopunroll` — unrolled loops, straight-line paths.
2. `test-projects/test-splitinvoke` — cross-package `invoke`, frame push/pop, return-in-branch.
3. `example-projects/hello-world` — a real (tiny) oracle.
4. `example-projects/kem-dem/kem-dem-cca-ssp` — the epic's primary target. Proofstep 0 is
   `equivalence Game_MON_CCA_PKE Game_MOD_CCA_PKE_Real_KEM` (`theorem/Proof.ssp:237`), oracles
   `PKGEN`, `PKENC`, `PKDEC`. `PKENC` has sampling *and* cross-package invokes into
   `KEM`/`DEM`/`Key`; `PKDEC` has the interesting branching. Use it to sanity-check that the path
   count is in the tens, not the thousands.

> **Never** run anything against `example-projects/4WHS` or `example-projects/yao` — the two slow
> projects in `example-projects/known-good-slow.txt`. See `docs/stories/00-overview.md` §7.

## 7. Notes / risks

- **The single biggest correctness risk** is the terminal game-state reconstruction (§4.5)
  diverging from `smt_write_back_state` + `smt_update_gamestate_pkgstate`. If the invariants
  disagree with the prover, everything downstream is noise. Prefer reusing the existing context
  helpers over re-deriving the datatype plumbing, and write the consistency test.
- Randomness counters: getting these wrong silently breaks `randomness-mapping` and the
  injectivity story. Cross-check against `build_rands`
  (`src/writers/smt/contexts/equivalence/emit.rs:1440`) and the zero-assert it emits.
- Path explosion: even without a solver, an oracle with 15 branch points has 32768 paths. That is
  why `max_paths` exists and why `execute_streaming` matters. Do not build a `Vec` of every path
  before checking the cap.
- Do not add solver calls here. Branch pruning is story 06's job; this story must stay
  solver-free and fast.

## 8. State handed to the next story

Story 06 will rely on:

- `crate::debug::exec::{Side, Step, Decision, Terminal, TerminalPath, execute,
  execute_streaming, ExecError}`.
- `TerminalPath { id, steps, decls, constraints, return_constraint, terminal }` and the guarantee
  that asserting `decls + constraints + return_constraint` on a solver that already has the base
  declarations (with `emit_constant_declarations(Some(oracle))`) is a complete, sound encoding of
  that one path.
- The `Decision` names, which story 06 and 07 render as `then` / `else` / `assert-holds` /
  `assert-fails` / `unwrap-some` / `unwrap-none`.

### Done — see `docs/stories/05-symbolic-executor-core-IMPLEMENTATION-REPORT.md`

`src/debug/exec.rs` implements exactly the surface above (`execute` / `execute_streaming` /
`Side` / `Step` / `Decision` / `Terminal` / `TerminalPath` / `ExecError`). `TerminalPath.id` is
left `""` for the driver to fill.

**Terminal reconstruction — what a cold session gets wrong (report §4):**

1. **Thread the game state through fresh SSA constants** (`<v!{side}!{n}!gamestate>`), one per
   step. Folding into a single term blows up: `smt_increment_gamestate_rand` /
   `smt_update_gamestate_pkgstate` each re-read the *entire* accumulator per field copied.
2. Order: `old` → `smt_increment_gamestate_rand` once per draw per non-zero counter (sorted by
   `sample_id`) → `smt_update_gamestate_pkgstate` once per folded instance (`game().pkgs`
   order). The prover interleaves these but the selectors are disjoint and re-folding an
   instance with final values is idempotent, so the net terminal state is identical.
3. Fold (and seed package state for) **exactly** entry ∪ every `Call` callee instance — the
   prover's unconditional-caller-write-back set. Untouched instances keep the old value.
4. `Sample` uses the **literal** counter from 0; this equals the prover's `(access-rand
   old)+k` term **only** under `build_rands`' `(assert (= (access-rand old) 0))`, which story 06
   emits. A standalone consistency check must add that assert.
5. `<return-{GI}-{O}>` name = `format!("<return-{}-{}>", game_inst.name(), inlined.oracle_name)`
   (`oracle_name` is the exported name). Apply `octx.set_renamed(export.alias())` before
   `smt_arg_name`.

**Consistency check (§5 "the important one") is deferred to story 06's `domino prove`
cross-check** (report §6) — story 06 must, first thing, verify per path that
`(=> (and constraints) (= <return-{GI}-{O}> <oracle-fn old consts args>))` holds for one small
oracle.
