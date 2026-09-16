# Story 04 — Games: instance clones, router, interfaces, experiment

**Epic:** EasyCrypt Export — see `docs/stories/easycrypt/00-overview.md`.
**Branch:** `amir/easycrypt-export`
**Depends on:** story 03 (package variants), and through it 01 and 02.
**Blocks:** 05, 06, 07, 08.

---

## 1. Why this story exists

Domino's composition is a wiring diagram; EasyCrypt has no such thing. This story turns each
composition into three artifacts: **instance clones** (so two instances of one package have
separate memory), a **router** module carrying the abort flag and exposing the exported oracles,
and an **experiment** that initializes the router and runs the adversary.

## 2. Inherited from earlier stories

### 2.1 From story 03

Package variants and their file/module names; the functor-parameter naming `P_<calleeInst>` and the
module-type naming for those parameters (story 03's report fixes it — match it exactly); `init`
signatures; that every package oracle returns an option and packages carry **no** abort flag.

### 2.2 Domino shapes (`src/package.rs`)

```rust
struct Composition { pkgs: Vec<PackageInstance>, edges: Vec<Edge>, exports: Vec<Export>,
                     name: String, consts: Vec<(String, Type)>, .. }
impl Edge   { fn from(&self) -> usize; fn to(&self) -> usize; fn sig(&self) -> &OracleSig;
              fn alias(&self) -> Option<&String>; fn name(&self) -> &str; }
impl Export { fn to(&self) -> usize;   fn sig(&self) -> &OracleSig;
              fn alias(&self) -> Option<&str>;    fn name(&self) -> &str; }
impl Composition { fn get_oracle_sigs(&self) -> Vec<OracleSig>; fn ordered_pkgs_idx(&self) -> Vec<usize>; }
```

`GameInstance` (`src/theorem.rs:19`) is `{ name, game: Composition, types, consts:
Vec<(GameConstIdentifier, Expression)> }`. **Several game instances share one composition** — emit
per composition, not per instance (overview §3).

### 2.3 Verified EasyCrypt facts for this story

Compiled end to end in the design session:

```
clone PkgProt as Pkg_Prot.                              (* no overrides needed *)
module KX_inst = Pkg_KX.KX(Pkg_Prot.Prot).              (* functor application of a clone *)
declare module A <: Adv { -GameH.G, -GameH.Pkg_KX.KX, -GameH.Pkg_Prot.Prot }.
```

Restrictions must name the **cloned module** (`Pkg_<inst>.<Variant>`), not a functor-application
alias. `clone` needs the theory required first (`require PkgKX.`).

## 3. Work to do

New files `src/writers/easycrypt/game.rs` and `src/writers/easycrypt/interfaces.rs`.

### 3.1 `Interfaces.ec` (one per theorem)

```
require import AllCore FMap Distr Int Types.

module type KX_i = { proc d_NewKey(ltk : bits_n option) : int option  … }.   (* one per package variant *)
module type Iface_Hybrid0 = { proc d_NewKey(…) : int option  … }.            (* one per export signature *)
module type Adv_Hybrid0 (O : Iface_Hybrid0) = { proc run() : bool }.
```

- **One module type per package variant**, listing *all* of that variant's defined oracles (not
  just the imported ones) — the callee module has them all, and this keeps the type independent of
  who calls it. `init` is **not** in it: routers call `init` on the concrete clone.
- **One game interface per distinct export signature list** across the theorem's compositions,
  named after the first composition (in theorem instance order) that has it, with a comment listing
  the others that reuse it. Compositions compared in an equivalence necessarily share one, which is
  what lets both sides take the same adversary.
- One `Adv_<X>` per game interface.
- Everything sorted deterministically; oracle order inside a game interface is the composition's
  `exports` order — story 07 emits per-oracle proof bullets **in this order**, so it is load-bearing.

### 3.2 `games/<Comp>.ec`

```
require import AllCore Distr FMap Int IntDiv Types.
require Interfaces KX Prot.                    (* package variant theories *)

clone KX   as Pkg_KX.                          (* one per package instance, ordered_pkgs_idx() *)
clone Prot as Pkg_Prot.

module Inst_KX = Pkg_KX.KX(Pkg_Prot.Prot).     (* only for functors; see below *)

module Game_Hybrid0 : Interfaces.Iface_Hybrid0 = {
  var abort_flag : bool

  proc init(b : bool) : unit = {
    abort_flag <- false;
    Pkg_Prot.Prot.init();
    Inst_KX.init(b);
  }

  proc d_NewKey(ltk : bits_n option) : int option = {
    var ec_r : int option <- None;
    if (!abort_flag) {
      ec_r <@ Inst_KX.d_NewKey(ltk);
      if (ec_r = None) { abort_flag <- true; }
    }
    return ec_r;
  }
  …one proc per export…
}.

module Exp_Hybrid0 (A : Interfaces.Adv_Hybrid0) = {
  proc run(b : bool) : bool = {
    var b' : bool;
    Game_Hybrid0.init(b);
    b' <@ A(Game_Hybrid0).run();
    return b';
  }
}.
```

Rules:

- **Clones**: one `clone <Variant> as Pkg_<inst>.` per package instance, in `ordered_pkgs_idx()`
  order, `require`d first. Instance names are mangled to a module name (`Pkg_` + mangled instance).
- **Functor application**: a variant with functor parameters gets
  `module Inst_<inst> = Pkg_<inst>.<Variant>(Pkg_<callee1>.<V1>, …)`, arguments in the order story
  03 fixed for that variant, resolved through the composition's `edges` (`edge.from() == inst`,
  grouped by `edge.to()`). A variant with **no** parameters gets no alias — call
  `Pkg_<inst>.<Variant>.<proc>` directly.
- **Router state is exactly one variable**, `abort_flag : bool`.
- **`init`** takes the composition's `consts` of boolean and value-integer type, in declaration
  order (width integers and `fn` consts are not arguments — they are types and global operators).
  It sets `abort_flag <- false` and calls each instance's `init` in `ordered_pkgs_idx()` order,
  passing that instance's parameter bindings translated as expressions (they may mention the
  router's `init` arguments). Instances whose variant has no `init` are skipped.
- **Export procs**: name from `Export::alias()` (falling back to `sig().name`), mangled; callee proc
  from `sig().name`, mangled; arguments and return type from `sig()`. The body is exactly the shape
  above — this is the only place the abort flag is read or written.
- The router carries `: Interfaces.Iface_<X>` so a signature drift fails at export-compile time
  rather than in a later proof.

## 4. Acceptance criteria

- [ ] `hello-world` exports a composition with **two clones of one variant** (`fwd`, `fwd2`) and a
      router whose two exported oracles target different clones.
- [ ] `4WHS` `Simple4WHS` exports `Hybrid0`, `Hybrid1`, `Hybrid2` and `PRF` compositions; golden
      files under `testdata/easycrypt/story04/`.
- [ ] `Interfaces.ec` reuses one game interface for `Hybrid0` and `Hybrid1` (same exports), with the
      reuse noted in a comment.
- [ ] A composition whose instance has imported oracles produces a functor application with the
      arguments in story 03's order.
- [ ] Generated `Types.ec` + `Interfaces.ec` + `packages/*.ec` + `games/*.ec` for 4WHS
      `Simple4WHS` **compile**: `easycrypt compile -I <out> <file>.ec` for each, in dependency
      order, exits 0. Test skips when `easycrypt` is absent.
- [ ] Deterministic output; `cargo build/test/clippy --workspace` clean.

## 5. How to verify

```bash
cargo test --workspace easycrypt
cd testdata/easycrypt/story04/4WHS
for f in Types Interfaces packages/*.ec games/*.ec; do easycrypt compile -I . -I packages -I games $f; done
```

Never run `domino prove`/`debug` on 4WHS.

## 6. Notes / risks

- **Restrictions name clones, not aliases.** Story 07 writes `{ -<Game>.Pkg_<inst>.<Variant>, … }`;
  record the exact strings in your report so 07 can reproduce them without re-deriving.
- **`Exp` takes the adversary only.** Unlike `~/Research/ec4whs`, the experiment is *not*
  parameterized by the game — the game is fixed per composition and the constants are `run`'s
  arguments. This is a deliberate difference from the manual translation.
- **Don't put the game-state record here.** It belongs to the invariant files (story 06); routers
  and packages never mention it.
- **Composition constants that are unused** still become `init` parameters. Keeping the signature
  positional and complete is what lets story 07 pass a game instance's bindings straight through.

## 7. State handed to the next story

Record in `04-…-IMPLEMENTATION-REPORT.md`: the file and module naming (`games/<Comp>.ec`,
`Game_<Comp>`, `Exp_<Comp>`, `Pkg_<inst>`, `Inst_<inst>`, `Iface_<X>`, `Adv_<X>`), the exact
restriction strings for each composition, the `init` parameter order per composition, the export
(and therefore proof-bullet) order per game interface, and the golden-file paths.
