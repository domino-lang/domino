# Epic: EasyCrypt Export (`domino easycrypt`)

> This is the epic overview. Every story under `docs/stories/easycrypt/` is self-contained, but
> read this file first in each new session — it carries the shared context, the settled design
> decisions, the testing strategy and the working agreement.
>
> Source of the requirement: `docs/easycrypt-export.md` (written by the project owner), as
> amended by the design session recorded in §3. **Where this file and `docs/easycrypt-export.md`
> disagree, this file wins** — several points in the plan turned out to be impossible in
> EasyCrypt, and §3 records what replaced them and why.

---

## 1. The problem

Domino proves equivalences by discharging SMT obligations with cvc5. EasyCrypt proves them with a
relational program logic and a human-written tactic script. The two describe the *same* games, so
the translation is mechanical — but doing it by hand is slow and error-prone. There is a manual
translation of the 4WHS project (`~/Research/ec4whs/simple` and `~/Research/ec4whs/full`,
about 9k lines) that took considerable effort and is already drifting from the Domino sources.

We want `domino easycrypt` to generate the boilerplate: types, packages, games, experiments,
invariants and the skeleton of each equivalence proof, leaving `admit` exactly where a human has
to think.

**The manual translation is inspiration, not a target.** Do not copy project-specific code out of
it. It uses records with named fields where Domino has anonymous tuples, it has no router module,
and its experiment is parameterized by the game. Where it differs from this epic, this epic wins.

## 2. What we are building

1. `domino easycrypt` — writes a compilable EasyCrypt project under `_build/easycrypt/<theorem>/`:
   `Types.ec`, `Interfaces.ec`, `Pkg_*.ec`, `Comp_*.ec`, and per equivalence
   `Eq_<Left>_<Right>.ec` + `Eq_<Left>_<Right>_Invariants.ec` — all in one flat directory
   (story 10; before it, package and game files sat in `packages/` and `games/`; story 14 renamed
   `Variant_*.ec` to `Pkg_*.ec`).
2. An **EasyCrypt AST** (`src/writers/easycrypt/ast.rs`) as the real artifact — text is only its
   rendering — so the symbolic-execution debugger can later run on the generated code.
3. `domino inline --easycrypt` and `domino debug --easycrypt` — the existing debugger machinery
   (`src/debug/`), driven by the generated EasyCrypt code instead of inlined Domino code.

Out of scope for this epic: randomness mappings, reductions, hybrid game hops, and deriving proof
tactics from execution paths. The generated proofs `admit` every oracle.

## 3. Design decisions (settled with the project owner — do not relitigate)

Everything in this table was verified against EasyCrypt `r2026.06-12-g7e192dd` by compiling test
files, or read out of this repository's source. §8 lists the evidence.

| Topic | Decision |
|---|---|
| **Instantiation** | **No abstract types and no abstract operators in generated packages.** A package instance is already monomorphic by export time (`src/packageinstance.rs:31`), so each package is emitted **specialised**. A **package variant** is one module per distinct assignment of a package's *integer and function* parameters; boolean parameters are not part of the key. This mirrors Domino's own SMT specialisation (`only_ints_and_funs`, `src/writers/smt/patterns/instance_names.rs:17`). **Amended by story 14:** the key is a package's *`Bits`-width integer* and *function* parameters only. A non-width integer parameter is already a module variable set by `init`, and how a package is *wired* no longer splits it into variants at all. |
| **Multiple instances** | Each package **instance** gets its own theory clone in its game file — no overrides. EasyCrypt clones theories, not modules, so a package theory contains just its module (plus, after story 14, its import interface). Cloning gives each instance its own memory. **Amended by story 14:** the clone is `clone Pkg_<Variant> as Cloned_Pkg_<inst>.` and *every* instance additionally gets a module `Pkg_Inst_<inst>` — a functor application when it imports oracles, a plain alias when it does not — so calls, state paths and adversary restrictions all name `Pkg_Inst_<inst>` with no variant component. |
| **Package imports** (story 14) | A package declares, **in its own file**, one `module type <Variant>_Imports` listing the oracles it expects, named by its *own* import names, and takes a single functor parameter `O`. A composition satisfies it by passing the callee's `Pkg_Inst_<callee>` directly (only when all of the caller's edges go to that one callee and none is aliased), otherwise by a composition-local adapter `Pkg_Imports_<inst>` that fans out to several instances. Packages therefore never depend on their callees' interfaces, and `Interfaces.ec` holds game interfaces only. |
| **`local` clones** | **Impossible.** A non-local module cannot depend on a local one (`module M cannot depend on local module Pkg_L.P`). Not needed either: a file is already a namespace. |
| **Type parameters** | **Unsupported.** A package instance with a non-empty `types { … }` block is a hard error. (`nprf` is the only project that uses them and it is not a target.) |
| **Package state** | **Module variables**, not one record per package. Records would force a copy-and-`{\| … with … \|}` dance at every table write, and EasyCrypt forbids two record types sharing a field name. |
| **Tables** | `fmap`. `T[k] <- Some e` → `T.[k] <- e`; `T[k] <- None` → `T <- rem T k`; an arbitrary `Maybe` right-hand side → `T <- if e = None then rem T k else T.[k <- oget e]`. |
| **Abort** | An oracle returning `T` in Domino returns `T option` in EasyCrypt; `None` is abort. An oracle with no return value returns `unit option` and returns `Some tt`. The abort **flag lives only in the router**, never in a package. |
| **Early return / abort mid-body** | ~~The export pipeline runs `treeify`, which already pushes the continuation of an `if` (and therefore of an `assert`) into both branches. `treeify` does **not** cover `Unwrap` and `InvokeOracle`, so the translator nests the rest of the block into the `else` of those two itself.~~ **Superseded by story 16.** EasyCrypt restricts us to one *exit point*, not one statement, so nothing is duplicated. `easycryptify` moves the continuation into the sole surviving branch where there is one (this is what `assert`, `Unwrap` and `InvokeOracle` all are), and guards it with a `ec_done` flag at a genuine join of two live paths. Its output is valid Domino with no `Abort` and a single trailing `Return`; oracle signatures become `Maybe(T)`. Story 03 §3.5 and the first two bullets of its §6 no longer apply. |
| **Pipeline** | ~~`EquivalenceTransform` — the existing `prove` pipeline, `run_treeify = true`.~~ **Amended by story 16:** `EasyCryptTransform` — the same pipeline with `easycryptify` in place of `treeify`, running last, after `tableinitialize`. `treeify` is unchanged and still serves the SMT writer via `EquivalenceTransform`. `domino inline/debug` **with** `--easycrypt` use `EasyCryptTransform`, so the debugger shows the code that is actually exported; **without** the flag they keep using `DebugTransform` unchanged, so a Domino listing still renders `assert` as `assert`. The transform, not a flag inside the IR, is what makes the two listings differ. |
| **Naming** | Deterministic mangling: lowercase-first names survive unchanged; uppercase-first names and EasyCrypt keywords get a `d_` prefix (`NewKey` → `d_NewKey`, `LTK` → `d_LTK`, `return` → `d_return`) — EasyCrypt requires `proc`/`var` names to start lowercase, which is the whole reason the prefix exists; `-` → `_` in SMT-derived names; modules are `Pkg_<inst>`, `Game_<comp>`, `Exp_<comp>`. A residual collision is a hard error. **Amended by story 10:** generated *theories* are `Variant_<X>` / `Comp_<X>`, which retires both stdlib-collision hacks. **Amended by story 14:** theories are `Pkg_<X>` / `Comp_<X>`; inside a game file, the clone is `Cloned_Pkg_<inst>`, the instance module `Pkg_Inst_<inst>` and the import adapter `Pkg_Imports_<inst>`; a package's import interface is `<Variant>_Imports` in the package's own file. |
| **Output layout** | **Amended by story 10: flat.** One directory per theorem, no `packages/`/`games/` subdirectories, so `easycrypt compile -I <dir>` needs a single `-I`. |
| **Games** | One game file per **composition** (not per game instance). Game instances appear only as the arguments of an `Eq_*` lemma. |
| **Experiment** | `Exp_<Comp>` per composition, in the game file. Its `run` takes the composition's boolean and value-integer constants in declaration order. Width integers become types; function constants become global operators. |
| **Invariants** | One invariant file per equivalence (this branch's grammar, `src/parser/ssp.pest:295`). Every `define-state-relation` becomes an operator `Domino_<name> (l, r)`; helper `define-fun`s become `Domino_<name>`. The assembled invariant is `params_inv l r /\ l.abort_flag = r.abort_flag /\ (!l.abort_flag => Domino_… )`. |
| **Game-state record** | Flat, one per game *instance*, declared in `Eq_*_Invariants.ec`, built inline at the `call` site from module variables. Fields are `pkg_<inst>_<field>` plus `abort_flag`. Never used by a router or package. |
| **Unsupported constructs** | Hard error with a source span: `Set`, `List`, `String`, group types, `while`, any loop `loopunroll` could not unroll, package type parameters, sampling anything but `Bits`. |
| **Proof skeleton** | v1 emits `byequiv => //. proc; inline. call (: inv …); last first. auto => />. smt(emptyE map_empty).` then `+ proc; inline. admit.` per oracle, in game-interface order. No path-derived tactics. The base case is a real `smt` call, not an `admit`, so a broken base case is visible. **Amended by story 13:** `byequiv` takes an explicit relational precondition `(: ={glob A} /\ <every run arg of both sides> ==> _) => //.`, which is what makes the same-composition base case actually discharge. **Amended by story 15:** that precondition names `arg`, not the individual parameters — one conjunct per side, `arg{1} = (v1, v2)` — because a lemma binder spelled like a `run` parameter silently shadows it and voids the conjunct. |
| **Debugger** | The EasyCrypt AST is the artifact; a **lowering** turns inlined EasyCrypt code into the debugger's existing IR (`src/debug/ir.rs`), so executor, solver, claims, HTML and `trace.json` are untouched. Labels are line numbers in the **EasyCrypt** listing. |
| **Reductions / hybrids / randomness mappings** | Skipped, with a note in the output. |
| **`flake.nix`** | **Not** modified. EasyCrypt comes from the developer's opam switch; tests that shell out to it skip when it is absent. |

## 4. Architecture at a glance

```
      domino easycrypt --theorem T
                 |
        EasyCryptTransform (easycryptify)         <- story 16; was EquivalenceTransform (treeify)
                 |
        +--------+-----------------------------------------+
        |                       |                          |
   types + exprs           packages + games           invariants (.smt2)
   (story 02)              (stories 03, 04)           (story 06)
        |                       |                          |
        +--------+--------------+--------------------------+
                 |
              EcAst  (story 01)  --render-->  *.ec  (story 05)
                 |                                     |
                 |                              Eq_*.ec skeleton (story 07)
                 v
        lowering to src/debug/ir.rs (story 08)
                 |
        domino inline --easycrypt (story 08)
        domino debug  --easycrypt (story 09)  -> existing executor + viewer
```

## 5. Stories and dependency order

| # | Story | File | Depends on |
|---|---|---|---|
| 01 | EasyCrypt AST, renderer and identifier mangling | `01-ec-ast-and-renderer.md` | — |
| 02 | Types, expressions and `Types.ec` | `02-types-and-expressions.md` | 01 |
| 03 | Package variants: modules, state, oracles, abort | `03-package-variants.md` | 02 |
| 04 | Games: clones, router, interfaces, experiment | `04-games-and-router.md` | 03 |
| 05 | `domino easycrypt` command and project layout | `05-easycrypt-command.md` | 04 |
| 06 | Invariant translation | `06-invariant-translation.md` | 02, 04 |
| 07 | Equivalence proof skeleton | `07-proof-skeleton.md` | 05, 06 |
| 08 | Lowering to the debugger IR + `inline --easycrypt` | `08-ec-ir-lowering.md` | 03, 04 |
| 09 | `domino debug --easycrypt` | `09-debug-on-easycrypt.md` | 08 |
| 10 | Flat layout and collision-free theory names | `10-flat-layout-and-theory-names.md` | 05, 07 |
| 11 | Shared package module types in `Interfaces.ec` | `11-shared-package-module-types.md` | 04, 10 |
| 12 | Render `None` without a type annotation | `12-unannotated-none.md` | 01, 10 |
| 13 | `byequiv` relational precondition | `13-byequiv-precondition.md` | 07, 10 |
| 14 | Package import interfaces, adapters and the `Pkg_` prefixes | `14-package-import-interfaces-and-prefixes.md` | 03, 04, 10, 11 |
| 15 | `byequiv` precondition via `arg`, not per-parameter conjuncts | `15-byequiv-arg-tuple-precondition.md` | 13, 14 |
| 16 | `easycryptify`: lowering early exits without duplicating code | `16-easycryptify.md` | 03, 04, 14 |
| 17 | Removing the `unwrap_N` temporaries and their duplicate guards | `17-unwrap-temporaries.md` | 16 |

Stories 01–05 are a walking skeleton: after 05 the 4WHS packages and games compile under
`easycrypt compile`. 06 may be done in parallel with 05. 08 may be done in parallel with 06/07.

Stories 10–15 are follow-ups on the implemented export (owner review after story 07); they are
independent of 08/09 and **should be done first**, because 10 relocates and renames every golden
file that 08 would otherwise inherit. Within 10–13: do 10 first, then 11/12/13 in any order. 15
supersedes story 13's rendering of the precondition and should be done after 13 and 14.

Stories 16–17 replace `treeify` in the export pipeline and change the shape of every generated
oracle body. Do them **before 08/09**: 08's listing labels and 09's execution paths are derived
from that shape, and doing them in the other order means redoing both. 16 first, then 17.

## 6. Working agreement (important)

- Implementation is done by **Sonnet in extra-high thinking mode**, **one story per session**,
  with the **context reset after each story**.
- Because of the context reset, **every story file is self-contained**. It restates the context it
  needs, names concrete files and signatures, and lists what earlier stories left behind. If while
  implementing you discover a fact a later story will need, add it to that story's "Inherited from
  earlier stories" section before you finish.
- Every story ends with **"State handed to the next story"**, recorded in
  `docs/stories/easycrypt/<NN>-…-IMPLEMENTATION-REPORT.md`. Keep it accurate — it is the only
  thing the next (cold) session knows about your work besides the code itself.
- Each story is one reviewable commit on branch `amir/easycrypt-export`.
- Do not expand scope. If something outside the story is broken, note it under "Notes for
  follow-up" and move on.

## 7. Testing strategy (applies to every story)

### Hard rules

> **Never run `domino prove` or `domino debug` against `example-projects/4WHS` or
> `example-projects/yao`.** Proving them takes hours.
>
> **`domino easycrypt` against 4WHS is fine and is the acceptance target** — export runs no
> solver. This is the one command exempt from the rule above.

### Ladder, fastest first

1. `cargo test --workspace` — golden-file tests over rendered `.ec` text under
   `testdata/easycrypt/story<NN>/`. The primary safety net for stories 01–04, 06, 08.
2. `example-projects/hello-world` — two packages, one composition with **two instances of the same
   package** (`fwd`, `fwd2`), so it exercises instance clones. Smallest end-to-end export.
3. `example-projects/simple-KEM-example` — the only project using a `Bits` **literal**
   (`Bits(256)`), so it exercises literal-width bits types.
4. `example-projects/kem-dem/kem-dem-cca-ssp` — real branching, sampling, cross-package invokes and
   a hand-written invariant; the target for stories 08 and 09.
5. `example-projects/4WHS` — the acceptance target for export (both theorems), and the project the
   manual translation exists for.

### Compiling the output

```bash
easycrypt compile -I <outdir> <file>.ec     # ~/.opam/easycrypt/bin/easycrypt, r2026.06-12-g7e192dd
```

Tests that shell out to `easycrypt` must **skip** (not fail) when it is not on `PATH`. Progress
output goes to stderr and is noisy; filter with `tr '\r' '\n' | grep -v '^\[.\] \['`.

### Build gotcha

```bash
cargo build --workspace          # correct
cargo build --release            # WRONG: does not relink the `domino` binary in crates/domino
```

## 8. Reference: facts about EasyCrypt and this codebase

Load-bearing for several stories; each story restates the ones it needs. Everything below was
verified in the design session, either by compiling a test file or by reading the source.

### 8.1 EasyCrypt facts (compiled against r2026.06-12-g7e192dd)

- **`clone` applies to theories, not modules.** `clone PkgP as Pkg_A with type … <- …, op … <- …`
  works; cloning the same theory twice gives two modules with separate memory. Grammar:
  `ecParser.mly:3465`.
- **There is no `theory X <- Y` clone override.** Only `type`, `op`, `pred`, `module`,
  `module type` (`ecParser.mly:3569-3607`). Abstract types therefore cannot be threaded through a
  chain of package theories — which is why packages are emitted specialised.
- **A public module cannot depend on a `local` one**: `module M cannot depend on local module
  Pkg_L.P`.
- **Record field names are globally unique per namespace**: a second record reusing a field name
  fails with `the symbol ltk_map already exists`. (Clones are separate namespaces, so per-instance
  clones are fine.)
- **Procedure and program-variable names must start lowercase.** `proc NewKey`, `var LTK` are parse
  errors; `var _U` is fine. `res` is a keyword.
- **Keywords** (from `ecLexer.mll`): `admit admitted forall exists fun glob let in for var proc if
  is match then else elif while assert return res equiv hoare ehoare phoare islossless async try
  first last do expect beta iota zeta eta logic delta simplify cbv congr change split left right
  case pose gen have suff elim exlim ecall clear wlog apply rewrite rwnormal subst progress trivial
  auto idtac move modpath algebra exact assumption smt coq check edit fix by reflexivity done solve
  replace transitivity symmetry seq wp sp sim skip call rcondt rcondf swap cfold rnd rndsem
  pr_bounded bypr byphoare byehoare byequiv byupto fel conseq exfalso inline outline interleave
  alias weakmem fission fusion unroll splitwhile kill eager axiom axiomatized lemma realize proof
  qed abort goal end from import export include local declare hint module of const op pred inductive
  notation abbrev require theory abstract section type class instance print search locate as clone
  with rename prover timeout dump remove exit fail time undo debug pragma`
- **Verified to compile**: tuple projections `` s.`1 ``…`` s.`10 ``; `None<:bits_n>`; `oget`;
  `m.[k <- v]` and `rem m k`; record literals inside a relational formula; qualified record
  projection across theories (`` l.`GS1.pkg_KX ``); functor application of a cloned module
  (`module KX_inst = Pkg_KX.KX(Pkg_Prot.Prot)`); `declare module A <: Adv { -GameH.Pkg_KX.KX, … }`
  with qualified clone names; `byequiv`/`call`/`admit` over such modules.
- **A logical binder silently shadows a program variable of the same name in a relational formula.**
  In `byequiv (: … /\ b{1} = b …)`, where `b` is both a lemma binder and the procedure's own
  parameter, EasyCrypt types `b{1}` as the *logical* `b`, discards the `{1}` tag and reduces the
  conjunct to `b = b`. The only signal is a warning, `unused memory '&1', while typing b`; the file
  still compiles. **`arg` is immune** — it is a program identifier a binder cannot shadow — which is
  why story 15 writes `arg{1} = (v1, v2)` instead. For a one-argument procedure `arg` is the value
  itself, not a one-tuple; for a zero-argument one it is `()`.
- **Module-type matching is structural and width-subtyping.** Two *independently declared*,
  structurally identical `module type`s are interchangeable: `module M (P : Fwd_v1_i)` applied to
  `R : Rand_i` compiles. A module with *more* procedures than the type demands also matches. So a
  duplicated module type never forces a second version of an importing package — deduplicating
  `Interfaces.ec` (story 11) is a readability change, not a correctness one. Story 14 deletes that
  section of `Interfaces.ec` outright; the same structural matching is what lets an adapter ascribed
  to an *uncloned* `Pkg_<V>.<V>_Imports` be passed to a functor expecting `Cloned_Pkg_<inst>.<V>_Imports`.
- **`module type X = Y.` is a parse error.** The aliasing form that works is
  `module type X = { include Y }.`, and a module matching `Y` still matches `X` through it.
- **A clone alias cannot share a name with the theory it clones**: `clone Pkg_KX as Pkg_KX.` fails
  with `the symbol Pkg_KX already exists`. This is why story 10 prefixes theories `Variant_`/`Comp_`
  and leaves `Pkg_<inst>` to the clone aliases.
- **A module alias denotes the same memory cells as its target, and so does a functor
  application.** `module Pkg_Inst_n = Cloned_Pkg_n.N.` gives `Pkg_Inst_n.s{m} = Cloned_Pkg_n.N.s{m}`
  by `done`, and `module Pkg_Inst_m = Cloned_Pkg_m.M(Arg).` gives
  `Pkg_Inst_m.ctr{m} = Cloned_Pkg_m.M.ctr{m}` by `done`. Adversary restrictions accept those short
  paths too (`declare module A <: Adv { -Pkg_Inst_m, -Pkg_Inst_n }.`). This is what lets story 14
  address every instance as `Pkg_Inst_<inst>` in the router, the invariants and the proofs.
- **A functor application can be passed as another functor's argument**, and a plain module can call
  into one (`r <@ Pkg_Inst_fwd.f();`) — both verified two levels deep (story 14 §2.1).
- **Module names and module-type names live in disjoint namespaces**: `module type Imports` beside
  `module Imports (O : Imports)` compiles. (Story 14 still avoids the shape, for the reader's sake.)
- **A theory clone may be named after anything but the theory it clones**, including
  `clone B as Pkg_Inst_n.` — the constraint below is only alias-vs-source.
- **Bare `None` is inferred everywhere the exporter emits it** — assignment to a typed local or
  state variable, comparison against an `fmap` get, inside a typed tuple, in an `op` body with a
  declared result type. It fails *only* with nothing to constrain it (`op bad = None.` →
  `this operator type contains free type variables`), which export never produces. Hence story 12.
- **`theories/crypto/PRF.eca` shadows a local `PRF.ec`** even when only the local directory is on
  `-I`, and even though `easycrypt config` does not report that directory in its load path. A
  *module* named `PRF` inside a theory is unaffected — only top-level theory names collide.
- **Working layout** (compiled end to end): `Types.ec` (concrete types and operators) →
  package theories that `require import Types` and contain only their module →
  a game file that clones each package per instance and defines the router →
  a theorem file with the section, the adversary declaration and the lemma.

### 8.2 Domino facts

- `PackageInstance` (`src/packageinstance.rs:18`) has `params: Vec<(PackageConstIdentifier,
  Expression)>` and `types: Vec<(String, Type)>`, and its `pkg` field is **already rewritten** —
  types substituted through oracles, state, params and imports (`rewrite_pkg_inst`,
  `src/theorem.rs:41`). Export therefore never has to substitute anything.
- `Theorem` (`src/theorem.rs:295`): `name`, `consts: Vec<(String, Type)>`, `instances:
  Vec<GameInstance>`, `assumptions`, `proofs`, `game_hops`, `pkgs`.
- `GameInstance` (`src/theorem.rs:19`): `name`, `game: Composition`, `types`, `consts:
  Vec<(GameConstIdentifier, Expression)>`.
- Pipeline (`src/transforms/theorem_transforms.rs:99`): `type_extract → deconstructinvoke →
  unwrapify → resolveoracles → samplify → loopunroll → sample_max_counter_extractor → returnify →
  [treeify] → tableinitialize`. `EquivalenceTransform` sets `run_treeify = true`;
  `DebugTransform` sets it to `false`.
- `tableinitialize` only touches `Identifier::Generated` locals — it inserts `<gen> <- empty`
  before the first write to a generated *local* table. It never touches package state.
- `Type::default_expression` (`src/types.rs:210`) gives Domino's state defaults: `0`, `false`,
  `None`, empty table, tuple-of-defaults, and the bits literal `0`. It **panics** for `Fn`, `Set`,
  `List`, `String`, group and user-defined types.
- Statements (`src/statement.rs:67`): `Abort`, `Return`, `Assignment`, `InvokeOracle`,
  `IfThenElse`, `For`. There is no `Assert` statement — an `assert` is parsed into an
  `IfThenElse` whose else-branch aborts, which is why `treeify` covers it.
- Types (`src/types.rs:103`) and expressions (`src/expressions.rs:436`) are listed in story 02.
- Writers live in `src/writers/{pseudocode,smt,tex}`; this epic adds `src/writers/easycrypt/`.
- The CLI is `crates/domino/src/cli.rs`, `enum Commands` (`:35`): `Latex`, `Prove`, `Format`,
  `Proofsteps`, `Debug`, `Inline`. Projects load via `DirectoryProject::load` /
  `find_project_root` (`src/project/directory.rs:70`, `:119`).
- Invariant files are hand-written SMT-LIB parsed by `src/util/smtparser` (grammar
  `smt.pest`), which already knows `define-fun`, `define-state-relation`, `define-lemma`,
  `define-game-invariant`, `define-package-invariant` and `sample-id`.
- On this branch an equivalence has **one** invariant spec (`src/parser/ssp.pest:295`:
  `equivalence = { … identifier ~ identifier ~ "{" ~ invariant_spec ~ equivalence_oracle+ … }`),
  so there is exactly one invariant file list per equivalence.
