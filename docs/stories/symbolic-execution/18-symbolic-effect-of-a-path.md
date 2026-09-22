# Story 18 — What the path actually did: symbolic return value and new state in the viewer

**Epic:** Symbolic-Execution Proof Debugger (`domino debug`) — see `docs/stories/00-overview.md`.
**Branch:** `amir/symbolic-execution-debugger`
**Depends on:** story 02 (`src/debug/ir.rs`), story 05 (`src/debug/exec.rs` — `SymState`,
`emit_terminal`), story 06 (`src/debug/driver.rs` — `LeftPath` / `RightPath`), story 07
(`src/debug/report.rs` — `trace.json`, the viewer), story 13 (`sec(title, body, defaultOpen, meta)`).
**Interacts with:** story 11 (per-path `smt/` files — this story does *not* change them), story 14
(parallel exploration must build the effect per worker, it is pure and side-effect free), story 16
(also edits `renderDetail`; whoever lands second reconciles the section order).
**Blocks:** nothing.

`TRACE_SCHEMA` is **6** today (story 13). This story bumps it by one — **6 → 7** if it lands next,
otherwise one more than whatever it finds. Record the number in the implementation report.

---

## 1. Why this story exists

The viewer answers *which lines ran* and *what SMT was asserted*. It does not answer the first
question a human actually asks at a failing pair:

> **What does this path compute, and what does it leave behind in the game state?**

Today the only place that answer exists is the raw path SMT — a flat SSA chain of
`(assert (= <v!left!27!SENTCTXT> (store <v!left!0!SENTCTXT> <v!left!5!ctr> (mk-some
<v!left!25!ctxt>))))` lines, plus a `<mk-game-…>` accumulator rebuilt three times, ending in one
`(assert (= <return-Prot-Run> (<mk-oracle-return-Prot-Prot-Run> <v!left!35!gamestate> (mk-return-value
<v!left!25!ctxt>))))`. Reading a left/right pair off that by hand is exactly the work the debugger
exists to remove — and it is work you have to redo for *every* pair.

Everything needed is already in `TerminalPath`: the encoding is a flat, acyclic, single-assignment
conjunction, so the definitions can simply be **unfolded back to the roots** — the oracle's own
arguments, the *old* game state, the game constants and the sample points. That is precisely "in
terms of the oracle input arguments and old state".

### What the owner asked for

> For the paths that end with a return (and do not abort), I want to see the symbolic returned
> value and new game state of the left and right oracles (both oracle return value and new state)
> in terms of the oracle input arguments and old state in the html viewer! The state and outputs
> may contain tables and the returned table if not created in the oracle, is usually the old table
> updated with some entries. You do not need to resolve whether it can be deduced that entries
> already exist or they are new entries or if several new entries are added, you do not need to
> check if all are distinct, you can simply list the new entries and the key value mappings and
> have a notation for saying the rest is the old table. Let's say you have table T then,
> `newT = oldT[x -> y, z -> t]` which means, newT is the same as oldT except with these two new
> entries!

Settled (do not relitigate):

| Decision | Choice |
|---|---|
| **Where** | The HTML viewer, as a new collapsible section, **open by default**. Also in `trace.json` so it is machine-readable. |
| **Which paths** | Terminals that **`return`**. Abort terminals get no effect block (§6). |
| **Both sides** | A right-path selection shows **left and right side by side**, in two columns — comparing them is the whole point of a `same-output` claim. A left-path selection shows the left column only. |
| **Roots** | Oracle arguments, `<<game-state-{GI}-old>>`, `<<game-consts-{GI}>>`, and sample terms. Nothing else is left unexpanded. |
| **Table notation** | Exactly the owner's: `T[k -> v, k2 -> v2]`, ASCII `->`, chain listed innermost-first. No reasoning about key distinctness, key freshness, or entry count — the notation is **purely syntactic**. |
| **Unchanged fields** | Named on one line (`unchanged: TESTED, sk, pk`), never expanded. A field counts as unchanged iff it is still bound to the SSA constant `initial_state` seeded it to. |
| **Sharing** | Sub-terms used more than once and longer than a threshold are hoisted into a `where` list rather than duplicated. No exponential blow-up, no unreadable one-liners. |
| **Fidelity** | The rendering is a **display**, not a second semantics. It is derived from the same terms the solver sees; when in doubt the `SMT asserted` section stays authoritative, and the effect block says so. |
| **No new flag** | Every run computes it. It is cheap (one linear pass per terminal). |
| **Not in `summary.txt` / stdout** | Out of scope; the viewer and `trace.json` only. |

## 2. Inherited from earlier stories — read before touching anything

### 2.1 The per-path encoding (story 05, `src/debug/exec.rs`)

`TerminalPath` carries `decls`, `constraints`, `return_constraint`. The `constraints` are of exactly
two shapes:

- **definitions** — `(assert (= <v!{side}!{n}!{basename}> <rhs>))`, pushed by `Executor::define`
  (`exec.rs:540`), always *after* everything `<rhs>` mentions (dependency order, acyclic, each SSA
  name defined exactly once); and
- **path conditions** — `(assert <cond>)` / `(assert (not <cond>))`, pushed at forks.

SSA names come from `Executor::fresh` (`exec.rs:528`): `v!left!25!ctxt` keeps the **source
basename** (`ctxt`), which is what makes a readable rendering possible at all.

### 2.2 What `initial_state` seeds (`exec.rs:1014`)

- every oracle argument → `(= <v!…!x> <arg-{GI}-{O}-x>)`;
- every package-state field of every folded instance → `(= <v!…!f> (<pkg-state-{Pkg}-{f}>
  (<game-{G}-pkgstate-{inst}> <<game-state-{GI}-old>>)))`;
- every *referenced* package const → `(= <v!…!c> (<pkg-consts-{Pkg}-{c}> (<pkgconsts-{G}-{inst}>
  <<game-consts-{GI}>>)))`.

These three shapes are the **roots** of the unfolding, and the state seeds double as the
"unchanged" oracle.

### 2.3 What `emit_terminal` has in hand (`exec.rs:906`)

At the moment a terminal is emitted, before any of it is flattened into the `<mk-game-…>`
accumulator:

- `st.pkg_state: HashMap<(pkg_inst, field), Identifier>` — the **final** SSA constant of every field;
- `st.rand_ctr: HashMap<sample_id, usize>` — how many draws happened, per sample point;
- the terminal's return `Expression`, which `to_smt(&st, e)` turns into a term over SSA constants;
- `self.fold_pkgs`, `self.gctx`, `self.sample_info`, `self.octx`.

> **This is the whole reason the story is small.** Do **not** parse the `<mk-game-…>` chain or the
> `return_constraint` back out — the structured facts are right there. The three `rebind_gs` steps
> exist only to keep the SMT flat; they carry no information the effect needs.

`self.sample_info.positions[sample_id]` is a `Position` (`src/transforms/samplify.rs:16`) with
`inst_name`, `oracle_name`, `sample_name`, `ty`.

### 2.4 The trace and the viewer (stories 06, 07, 13)

`LeftPath` (`driver.rs:345`) and `RightPath` (`driver.rs:363`) are built in
`explore_paths`/`check_pair` (`driver.rs:911`) and serialised into `trace.json`; `report.rs`
inlines that JSON into a self-contained `index.html`. `renderDetail` (`report.rs:942`) appends
sections built by `sec(title, body, defaultOpen, meta)` (`report.rs:756`), each persisting its
open/closed state under `localStorage["domino.debug.sec." + title]`.

`trace.json` and `index.html` are **byte-deterministic across two runs** — every map this story
iterates must therefore be ordered (§3.2).

## 3. Work to do

### 3.1 New module `src/debug/effect.rs`

Add `pub mod effect;` to `src/debug/mod.rs`. The module owns the data, the unfolding and the
rendering; it must not depend on the driver or the report.

```rust
/// What one returning path computed, expressed over the oracle's arguments, the
/// old game state, the game constants and the sample points.
///
/// Every string in here is a *rendering* — human-facing, deliberately lossy (see
/// `render`'s rewrite table). The authoritative encoding is the path's SMT.
#[derive(Debug, Clone, Serialize)]
pub struct PathEffect {
    /// The rendered return value. `None` for `return` with no value (rendered as
    /// `()` by the viewer) — this whole struct is `None` for an abort.
    pub returns: Option<String>,
    /// One entry per folded package instance, in game-declaration order.
    pub state: Vec<PkgEffect>,
    /// Sample points whose counter advanced, in sample-id order.
    pub rand: Vec<RandEffect>,
    /// Shared sub-terms hoisted out of the strings above, in dependency order.
    pub wheres: Vec<Binding>,
    /// A term hit `MAX_TERM_CHARS` and was elided with `…`.
    pub truncated: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct PkgEffect {
    pub pkg_inst: String,
    /// Fields whose final SSA constant differs from the seeded one, in package
    /// declaration order.
    pub changed: Vec<FieldEffect>,
    /// Field names still bound to their seed, in package declaration order.
    pub unchanged: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FieldEffect {
    pub field: String,
    /// The flat rendering, e.g. `old.Prot.SENTCTXT[old.Prot.ctr -> ctxt]`.
    pub value: String,
    /// Set when `value` is a `store` chain, so the viewer can put one entry per
    /// line for a wide table. `base` is the rendered chain base.
    pub table: Option<TableUpdate>,
}

#[derive(Debug, Clone, Serialize)]
pub struct TableUpdate {
    pub base: String,
    pub entries: Vec<Entry>,   // { key: String, value: String }
}

#[derive(Debug, Clone, Serialize)]
pub struct RandEffect {
    /// `Prot.Run.encaps_rand`
    pub point: String,
    /// Rendered type, e.g. `Bits(256)`.
    pub ty: String,
    /// How many draws this path made.
    pub draws: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct Binding { pub name: String, pub value: String }
```

`TerminalPath` (`exec.rs:156`) gains, after `terminal`:

```rust
/// What this path computed, for the viewer (story 18). `None` for an abort
/// terminal. Pure display — never fed to the solver.
pub effect: Option<PathEffect>,
```

### 3.2 Building it — `exec.rs::emit_terminal`

Insert a step between the current step 2 (folding package states) and step 4 (the return term) —
or, cleaner, compute it from `st` **before** the `rebind_gs` bookkeeping starts, since none of that
bookkeeping is an input. Order matters only for readability of the diff.

1. **Definition map.** Scan `st.constraints` once, in order, matching `(assert (= <atom> rhs))`
   where `<atom>` is an `SmtExpr::Atom` starting `<v!`; collect `HashMap<&str, &SmtExpr>` plus a
   `Vec` of names in definition order. Path conditions are skipped — they are the *reason* the path
   was taken, already shown by `Path — left/right`, and are not part of the effect.

   > Rebuilding the map here (rather than maintaining one in `SymState`) keeps the per-fork clone
   > cheap — `SymState` is cloned at **every** branch, and a `HashMap<String, SmtExpr>` in it would
   > be a real regression. Do not move it.

2. **Seeds.** `Executor` gains `state_seeds: HashMap<(String, String), String>` — the SSA name each
   `(inst, field)` was seeded to in `initial_state`. A field is **unchanged** iff
   `st.pkg_state[&key].smt_identifier_string() == state_seeds[&key]`.

3. **Roots.** The return value (`to_smt(&st, e)` for `Terminal::Return { value: Some(e) }`) and the
   final SSA constant of every changed field.

4. **Order.** Package instances in `self.fold_pkgs` order (which comes from `game().pkgs` — stable);
   fields in `pctx.pkg().state` declaration order (the same order `reconstruct_pkg_state` uses);
   sample points sorted by `sample_id`. **Never iterate a `HashMap` into the output.**

5. Aborts: `effect = None`. `Terminal::Return { value: None }`: `returns = None`, state and
   randomness still computed.

### 3.3 The renderer

A recursive `SmtExpr → String` over the definition map. Two passes:

**Pass 1 — reference counting.** Walk the roots, expanding SSA atoms, and count how many times each
SSA name is reached. (Count reaches, not nodes: stop at an already-counted name, then bump it.)

**Pass 2 — render.** An SSA reference is **hoisted** into `wheres` iff it is reached ≥ 2 times *and*
its own rendering is longer than `INLINE_MAX_CHARS = 12`; otherwise it is inlined. Hoisted bindings
are named by the SSA basename (`v!left!25!ctxt` → `ctxt`), disambiguated `ctxt#2`, `ctxt#3`… on
collision, and emitted in dependency order.

> The threshold is what keeps `old.Prot.ctr` (12 chars, used four times) inline while
> `encaps(old.Prot.pk, rand#0).1` (used three times) gets a name. Tune it once against the
> goldens in §3.7; do not make it a flag.

Rewrite table — applied bottom-up, so the rules compose:

| SMT | rendered |
|---|---|
| `(store T k v)`, chains thereof | `T[k -> v, k2 -> v2]` — innermost store first (§3.4) |
| `(select T k)` | `T[k]` |
| `((as const (Array …)) mk-none)` | `{}` (the empty table) |
| `(mk-some x)` | `Some(x)`; bare `x` in a table-value position (§3.4) |
| `mk-none`, `(as mk-none (Maybe τ))` | `None` |
| `(maybe-get x)` | `unwrap(x)` |
| `(mk-tupleN a b …)` | `(a, b, …)` |
| `(elN-i x)` | `x.i` |
| `(elN-i (mk-tupleN a …))` | the *i*-th element directly — **reduce before rendering** |
| `(<<func-f>> a b)` | `f(a, b)` |
| `(<pkg-state-{P}-{f}> (<game-{G}-pkgstate-{I}> <<game-state-{GI}-old>>))` | `old.{I}.{f}` |
| `(<pkg-consts-{P}-{c}> (<pkgconsts-{G}-{I}> <<game-consts-{GI}>>))` | `{c}` |
| `<arg-{GI}-{O}-{x}>` | `{x}` |
| `(__sample-rand-{GI}-{τ} (sample-id "I" "O" "name") i)` | `name#i` inline; the `where` line spells it out as `sample {τ} @ I.O.name #i` |
| `(= a b)` / `(not (= a b))` | `a == b` / `a != b` |
| `(+ a b)`, `(- a b)`, `(and …)`, `(or …)`, `(not a)` | `a + b`, `a - b`, `a && b`, `a \|\| b`, `!a` |
| `(ite c a b)` | `if c then a else b` |
| anything else | `head(arg, …)`, with the `<`…`>` name brackets stripped |

Everything unrecognised must still render — as `head(args…)`, never a panic and never a silent
drop. A new datatype in the prover must degrade to something ugly but truthful.

**Caps.** `MAX_TERM_CHARS = 2000` per rendered string and `MAX_WHERES = 40`. On overflow, cut with
`…`, set `truncated`, and let the viewer show a one-line note pointing at `SMT asserted`. This is
the only defence against a pathological deep path; it must never abort a run.

### 3.4 Tables — the owner's notation, precisely

`bind_fresh` (`exec.rs:553`) emits a table write as `(store <base_ssa> <index> <value>)` and rebinds
the *base*. So a field written twice is a nested chain, outermost = last write.

Flatten the chain, then print the base once and the updates **in write order**:

```
old.Prot.SENTCTXT[old.Prot.ctr -> ctxt]
old.Corr_reduction.RECEIVEDKEY[old.Corr_reduction.ctr -> decaps(unwrap(old.Corr_KEM.sk), ctxt)]
T[k -> v, k2 -> v2]
```

Rules, kept deliberately dumb — this is the owner's explicit instruction:

- **No** key-distinctness reasoning. If the same key is written twice, both entries are listed, in
  order; the later one wins by SMT semantics and the viewer says nothing about it.
- **No** "is this a new entry or an overwrite" analysis. None is available and none is needed.
- The base is whatever the chain bottoms out at, rendered by the same renderer: usually
  `old.{inst}.{field}`, but `{}` for a table built in the oracle, or another binding's name.
- Table values are `Maybe` in SMT; in **value position** strip one `mk-some` (`k -> v`, not
  `k -> Some(v)`) and render `mk-none` as `k -> None` (an explicit delete).
- A field whose new value is *not* a store chain renders as an ordinary term — no special case.

### 3.5 `driver.rs` — into the trace

- `TRACE_SCHEMA` += 1.
- `LeftPath` and `RightPath` gain `pub effect: Option<PathEffect>`, placed **immediately after
  `terminal`**, filled from `lp.effect` / `rp.effect` at `driver.rs:911` and in the right-path
  construction. `PrunedBranch` gains nothing — a prune never reached a terminal.
- Nothing else in the driver changes: no new solver calls, no change to verdicts, pruning, path
  ids, `summary.txt` or the stdout tree.

### 3.6 `report.rs` — the viewer section

One new section, appended **after `Path — right` and before `Claim assertion`** — the effect is the
answer to "what did this path do", and it is what you read first when a goal fails:

```js
detail.appendChild(effectSec(lp, isRight ? rp : null));
```

- Title `Effect — return value & new state`, `defaultOpen = true`.
- `sec-meta`: `returns 1 value · 5 of 8 fields changed` (one side) or `left: 5/8 · right: 5/8`.
- Body: a two-column grid (`display:grid; grid-template-columns:1fr 1fr; gap:…`) headed by the
  game-instance names when a right path is selected; a single column otherwise. Below ~900px the
  grid collapses to one column, left above right.
- Each column, in order: `returns` (monospace, the term), `state` (one sub-block per package
  instance: `field` in a narrow left cell, rendered value in a `<code>` cell that wraps; then the
  `unchanged: …` line, dimmed), `randomness` (`Prot.Run.encaps_rand +1`, omitted when the path drew
  nothing), `where` (dimmed, monospace, `name = value` per line, omitted when empty).
- A `FieldEffect` with `table` and ≥ 2 entries renders one entry per line:
  `base[` / `  k -> v,` / `  k2 -> v2 ]`.
- If either side is `truncated`, a dimmed note: `term elided — see SMT asserted for the exact
  encoding`.
- If a selected path aborts, its column reads `aborts at L<n> — no return value` and nothing else.
- Reuse the existing `.sec` / `.sec-body` CSS. New classes get the `eff-` prefix. **No new colours**
  beyond the existing dimmed/`code` tokens, and the section must be legible in both themes.

### 3.7 Tests

**Unit (`effect.rs`)**, over hand-built definition maps — fast, no project, no solver:
store-chain flattening (single, nested, repeated key, non-`old` base, `{}` base); `mk-some` /
`mk-none` in value position; `(el3-1 (mk-tuple3 …))` reduction; old-state accessor → `old.I.f`;
package const → `c`; `<arg-…>` → name; sample term inline vs. `where` spelling; the hoisting
threshold (a term used twice and 13 chars long is hoisted, 12 chars is not); name collision →
`x#2`; `MAX_TERM_CHARS` truncation sets `truncated` and does not panic; an unknown head renders as
`head(args…)`.

**Executor (`exec.rs`)**:
- `effect_is_none_for_abort_terminals`.
- `unchanged_fields_are_not_expanded` — `hello-world` `UselessOracle`.
- `golden_simple_kem_run_left_2` — the rendered effect of `simple-KEM-example` `KEM_Proof`
  proofstep 0, oracle `Run`, left path #2, against `testdata/story18/simple_kem_run_left2.txt`:

  ```text
  returns  ctxt
  state  Prot
    SENTCTXT      old.Prot.SENTCTXT[old.Prot.ctr -> ctxt]
    SENTKEY       old.Prot.SENTKEY[old.Prot.ctr -> encaps(old.Prot.pk, rand#0).2]
    RECEIVEDCTXT  old.Prot.RECEIVEDCTXT[old.Prot.ctr -> ctxt]
    RECEIVEDKEY   old.Prot.RECEIVEDKEY[old.Prot.ctr -> decaps(unwrap(old.Prot.sk), ctxt)]
    ctr           old.Prot.ctr + 1
    unchanged: TESTED, sk, pk
  randomness
    Prot.Run.encaps_rand  +1
  where
    rand#0 = sample Bits(256) @ Prot.Run.encaps_rand #0
    ctxt   = encaps(old.Prot.pk, rand#0).1
  ```

  and its right-hand partner `#2.1`, which must come out as (note `Corr_KEM` wholly unchanged, and
  the `el3-i`/`mk-tuple3` round-trip through the inlined `ENC_and_DEC` reduced away):

  ```text
  returns  ctxt
  state  Corr_KEM
    unchanged: sk, pk
  state  Corr_reduction
    SENTCTXT      old.Corr_reduction.SENTCTXT[old.Corr_reduction.ctr -> ctxt]
    SENTKEY       old.Corr_reduction.SENTKEY[old.Corr_reduction.ctr -> encaps(old.Corr_KEM.pk, rand#0).2]
    RECEIVEDCTXT  old.Corr_reduction.RECEIVEDCTXT[old.Corr_reduction.ctr -> ctxt]
    RECEIVEDKEY   old.Corr_reduction.RECEIVEDKEY[old.Corr_reduction.ctr -> decaps(unwrap(old.Corr_KEM.sk), ctxt)]
    ctr           old.Corr_reduction.ctr + 1
    unchanged: TESTED
  randomness
    Corr_KEM.ENC_and_DEC.encaps_rand  +1
  where
    rand#0 = sample Bits(256) @ Corr_KEM.ENC_and_DEC.encaps_rand #0
    ctxt   = encaps(old.Corr_KEM.pk, rand#0).1
  ```

  (The plain-text shape above is the **test fixture's** rendering — a small helper in the test, not
  a product surface. The product surface is `PathEffect` + the viewer. If the implementation's
  spacing differs, update the fixture, not the notation.)

- `golden_kem_dem_pkenc_left_1` — exercises **oracle arguments** (`m0` / `m1` appear as bare names)
  and a package instance with no state fields at all.

**Driver**: `trace_carries_an_effect_for_every_returning_path` (and `null` for aborts), schema
bumped, and `trace.json` still byte-identical across two runs.

**Report**: `synthetic_run` gains an effect on one left and one right path; assert `index.html`
contains the section title and one `->` table update.

## 4. Acceptance criteria

- [ ] On `simple-KEM-example` `KEM_Proof` proofstep 0 oracle `Run`, selecting right path `#2.1`
      shows both columns, and every table field reads `old.<inst>.<field>[<key> -> <value>]` with
      no `<v!left!…>`, no `<pkg-state-…>`, no `store`, and no `mk-some` anywhere in the section.
- [ ] Every term in the section is expressed only in terms of oracle arguments,
      `old.<inst>.<field>`, package constants, sample points, literals and `where` names
      introduced in the same section.
- [ ] `unchanged: …` lists exactly the fields whose final SSA constant is the seeded one; changing
      a field on one path and not another moves it between the lists.
- [ ] A path that draws randomness lists each sample point once with its draw count; a path that
      draws none has no `randomness` block.
- [ ] Abort paths show `aborts at L<n> — no return value` and no state block; `trace.json` has
      `"effect": null` for them.
- [ ] `trace.json` at the new schema carries `effect` on `LeftPath` and `RightPath`, and is
      **byte-identical across two runs** of an unchanged project (proves nothing iterates a
      `HashMap`).
- [ ] Verdicts, path counts, prune counts, solver-call counts, `summary.txt`, the stdout tree and
      the `smt/` files are **bit-for-bit unchanged** by this story on `kem-dem` PKENC.
- [ ] `kem-dem` PKENC wall-clock does not regress by more than 10%, and `trace.json` grows by less
      than 2× (record both numbers in the implementation report).
- [ ] No term rendering panics on any project in `example-projects/known-good.txt`; an unrecognised
      head degrades to `head(args…)`.
- [ ] The section is open by default, persists its open/closed state like every other `sec`, and
      collapses to one column on a narrow window.
- [ ] `cargo build --workspace` / `test` / `clippy --workspace` clean, and with
      `--features cvc5-lib`.

## 5. How to verify

```bash
source ~/.cache/domino/cvc5-lib-env.sh
cargo build --workspace --features cvc5-lib
D=$PWD/target/debug/domino

# the table showcase — small, fast, two packages on the right
cd example-projects/simple-KEM-example
$D debug --proof KEM_Proof --proofstep 0 --oracle Run --claim same-output --smt all
xdg-open _build/debug/KEM_Proof/Prot-H1_kem_correctness_real/Run/same-output/index.html
#   → select right path #2.1; compare the two columns against smt/2/left.smt2 and smt/2/1.smt2

# arguments + a stateless package instance
cd ../kem-dem/kem-dem-cca-ssp
O=_build/debug/kem_dem_cca_ssp/Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM/PKENC/same-output
cp $O/trace.json /tmp/a.json
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
diff <(jq 'del(.schema,.left_paths[].effect,.left_paths[].right_paths[].effect)' /tmp/a.json) \
     <(jq 'del(.schema,.left_paths[].effect,.left_paths[].right_paths[].effect)' $O/trace.json)
#   → empty: this story changed nothing but the effect fields and the schema number

# determinism
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
cp $O/trace.json /tmp/b.json
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKENC --claim same-output
diff /tmp/b.json $O/trace.json          # byte-identical

# an abort path
$D debug --proof kem_dem_cca_ssp --proofstep 0 --oracle PKDEC --claim equal-aborts
jq '[.left_paths[] | select(.terminal.is_abort) | .effect] | unique' $O/../PKDEC/equal-aborts/trace.json
#   → [null]
```

> **Never** run `debug`/`prove` against `example-projects/4WHS` or `example-projects/yao`.
> Build with `cargo build --workspace`, not `cargo build --release` — a bare release build never
> relinks the `domino` binary.

## 6. Notes / risks

- **This is a display, not a semantics.** Nothing computed here is ever asserted, and no verdict may
  depend on it. If the rendering and the SMT ever disagree, the SMT is right and the renderer has a
  bug. Say so in the section itself (a one-line dimmed footer is enough) so nobody debugs the
  pretty-printer instead of the proof.
- **Aborts are out of scope by decision, not by cost.** The builder is terminal-agnostic — an
  aborting path still has a well-defined final state, and `smt_construct_abort` carries it. The
  owner asked for returns; wiring aborts on later is a viewer line plus dropping the `None`, and a
  future story can do it if the state on the abort path turns out to matter for `equal-aborts`.
- **Blow-up is real.** A deeply nested path with a value used many times is what `wheres` and the
  caps exist for. Do not "improve" the renderer into full inlining; the goldens are the contract.
- **`SymState` stays lean.** Rebuilding the definition map at the terminal is deliberate
  (§3.2 note). A map in `SymState` would be cloned at every fork and would show up on PKENC.
- **Story 16 also touches `renderDetail`** (executed-line painting in the listings). The two are
  independent; whoever lands second keeps both sections and the order in §3.6.
- **Story 14 (parallel exploration)** needs nothing here: `PathEffect` construction is pure, uses
  only the path's own `SymState`, and holds no solver handle.
- **Do not widen scope.** No effect block in `summary.txt` or on stdout, no diffing of the two
  columns (highlighting *where* left and right differ is a fine follow-up story, not this one), no
  new CLI flag, no changes to the `smt/` files.

## 7. State handed to the next story

Record in `docs/stories/18-…-IMPLEMENTATION-REPORT.md`: the new `TRACE_SCHEMA` number, the
`PathEffect` field layout as implemented and its serialised position in `LeftPath`/`RightPath`, the
final `INLINE_MAX_CHARS` / `MAX_TERM_CHARS` / `MAX_WHERES` values and why, the rewrite rules that
turned out to be missing from §3.3's table, the PKENC runtime and `trace.json` size before/after,
and any term shape that had to fall back to `head(args…)`.
