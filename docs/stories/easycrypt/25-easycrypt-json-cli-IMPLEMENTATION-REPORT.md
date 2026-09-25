# Story 25 — implementation report

## Where it lives

- Repository: the EasyCrypt clone `easycrypt/` (its own git repo), branch
  `amir/domino-easycrypt-integration`, commit `b2511afa` on top of `1e2d06ec`
  (`r2026.09-8-g1e2d06ec`). Not pushed.
- Format: **`domino-json/1`**, specified in `easycrypt/doc/json-output.md` (in the clone). Story 26
  is written against that file.

## Build and binary

```bash
cd easycrypt
dune build src/ec.exe                 # ~20 s warm, ~1 min cold
ln -sf src/ec.exe ec.native           # what `make` does; the clone's .gitignore hides it
codesign -f -s - src/ec.exe           # macOS arm64, as the Makefile does
```

**`DOMINO_EASYCRYPT=<domino>/easycrypt/ec.native`**, run as `ec.native cli -json [-I dir]`.

- It must be invoked under the name `ec.native` (the symlink). A binary named `ec.exe` invoked by
  its absolute path under `_build/default/src/` does not find the theories
  (`cannot locate theory Pervasive`): `EcRelocate` decides local-vs-installed from the executable
  name and expects `theories/` beside it.
- Run it from a directory that has no `easycrypt.project`: the clone's own pins `Z3@4.16` and
  `CVC5@1.1`, which are not installed, and EasyCrypt then dies with an assertion failure in
  `ecUtils.ml:239`.
- `~/.opam/easycrypt/bin/easycrypt` was not touched (it has no `-json`).

## Protocol essentials for stories 26/27

- Input: sentences on stdin, `undo N.`, `exit.`. **One JSON line on stdout per sentence**, no
  prompt. The process moves its JSON stream to a private duplicate of fd 1 and re-points fd 1 to
  stderr; anything written through `Format.std_formatter` (`print`, `search`, `locate`) is captured
  into `messages` (`info`).
- Answer: `{"version", "state", "status": "ok"|"error"|"interrupted", "error"?: {"loc": {"start",
  "end"} | null, "msg"}, "messages": [{"level","text"}], "proof": null | {"goals": [...]}}`.
  - `state` is the undo depth after the sentence; `undo N.` gives back state `N`'s exact `proof`.
  - `error.loc` offsets are relative to the sentence start (as `-emacs`).
  - `proof` is present on errors too (goals as they still are). `null` = no active proof; `[]` = done.
  - The copyright banner and startup warnings arrive in `messages` of the **first** answer.
  - EOF is an implicit `exit.` and is answered by one more line.
  - SIGINT during a command: `status: "interrupted"`. SIGINT while idle: no answer at all.
- Goal: `{"id" (1-based ordinal), "tvars", "hyps": [{"name","ident":{"name","tag"},"kind":
  "var"|"mem"|"modty"|"hyp"|"abs_st", + type|memtype|modtype|form|body}], "concl": FORM, "text"}`.
  Hyps are in display order; `name` is the displayed (valid in a tactic) name.
- Every tree node has `kind`, `pp` (one line, correct memory context) and children. FORM nodes also
  have `ty`. Program-logic kinds: `equivS` (`left`/`right` = `{mem, ident, memtype:{arg, locals
  [{name,type}]}, stmt:[INSTR], stmt_pp}`, `pre`, `post`), `equivF`, `hoareS/F`, `phoareS/F`
  (`cmp`, `bd`), `ehoareS/F`, `eagerF`, `pr`. INSTR kinds: `asgn rnd call if while match raise
  abstract` (`if`: `cond`, `then`, `else`; `asgn`/`rnd`: `lvalue`, `expr`; `call`: `lvalue`,
  `proc` = `{path, top, name, pp}`, `args`).
- Operators: `{"kind":"app","op":"<qualified path>","head":FORM,"args":[...]}`; `inv` is
  `Top.<Eq file theory>.inv`. `op` is `null` when the head is not a plain operator.
- Quantifiers: `{"kind":"quant","quantifier":"forall"|"exists"|"lambda","binders":[{"name","ident",
  "kind":"type"|"mem"|"modty","type"...}],"body"}`; the same-named binders differ by `ident.tag`.

Sample (abridged, pRHL after `proc; inline *.` on two copies of a procedure with nested `if`/`<$`):

```json
{"version":"domino-json/1","state":6,"status":"ok","messages":[],"proof":{"goals":[{"id":1,
 "concl":{"kind":"equivS","pp":"equiv[ ... : a{1} = a{2} ==> b{1} = b{2}]",
  "left":{"mem":"&1","memtype":{"arg":null,"locals":[{"name":"a",...},{"name":"b",...}]},
   "stmt":[{"kind":"if","pp":"if (a = 0) ...","cond":{"kind":"app","pp":"a = 0","op":"Top.Pervasive.="},
            "then":[{"kind":"rnd","pp":"b <$ {0,1};",...}],"else":[{"kind":"if",...}]}]},
  "right":{...},
  "pre":{"kind":"app","pp":"a{1} = a{2}","op":"Top.Pervasive.=","args":[{"kind":"pvar","name":"a","mem":"&1"},...]},
  "post":{"kind":"app","pp":"b{1} = b{2}",...}}}]}}
```

## Acceptance results

- kem-dem (`kem-dem-cca-ssp`, exported tree copied out of the clone dir, fed whole on stdin to
  `cli -json -I .`): 20 sentences, 20 valid JSON lines, no stray output. After `proc; inline.` on
  `PKENC` both programs are instruction trees with the same nesting as EasyCrypt's text (7-level
  `if` nesting, `rnd r3 <$ dbits_kencr`, argument/return copies present), `pre` is
  `((m0{1}, m1{1}).`1 = ...) /\ inv {|...|} {|...|}` and `post` is `ec_result{1} = ec_result{2} /\
  inv ...` with `inv` an `app` whose `op` is `Top.Eq_..._Invariants.inv`. After `call (...); last
  first.` there are **4** goals, each with its hyps; other states have 3 and 2.
- Sizes: a line is 3 KB for the lemma statement, 30 KB after `byequiv`, 190-360 KB for the
  `proc; inline` goals with `inv` record literals (each node repeats its `pp`; nothing truncated).
- `forall` binders, error with location, `undo` exactness, multiple goals with their own hyps,
  `inv` as an application, hoare and procedure-level judgements, framing (one line per sentence,
  `print` captured, EOF): `python3 tests/json/check.py` in the clone, 15 tests, all pass (~11 s).
- EasyCrypt's own `unit` suite (`runtest ... unit`, 108 files) passes with the new binary. It
  needed `easycrypt.project` temporarily pointed at the installed prover versions
  (`CVC5@1.3.4`, `Z3@4.13.4`); the file was restored, not committed.
- SIGINT verified by hand: `by smt().` interrupted after 1 s gives `interrupted`, state unchanged,
  goals kept; an idle SIGINT gives no line.

## Size of the patch

`src/ecPrinting.ml` +386 (serializer `PPJson`), `src/ecTerminal.ml` +137, `src/ec.ml` +4,
`src/ecOptions.ml` +5, `src/ecOptions.mli` +1, `src/ecCorePrinting.ml` +4, `src/ecTerminal.mli` +1:
about 540 lines of OCaml, plus `doc/json-output.md` (227) and `tests/json/check.py` (~240).

## §8.1 re-verification on r2026.09-8-g1e2d06ec

Unchanged: clone of theories twice; `theory X <-` aside, all override kinds; a public module cannot
depend on a `local` one (`module P cannot depend on local module L`); record field names global
(`the symbol fa already exists`); `proc NewKey` / `var LTK` parse errors, `var _U` fine;
`module type X = Y.` parse error and `{ include Y }` fine; `clone T as T.` fails; free `None`
fails, inferred `None` fine; tuple projection `.`10`, `m.[k <- v]`, `rem`; a module alias has the
same memory as its target; the binder-shadowing warning (`unused memory `&1', while typing b`);
`seq` past the end errors (`invalid split index`); `rnd` not on the last instruction fails
(`invalid last instruction`); `if.` gives 3 goals; `sp.` consumed both prefixes; after
`proc; inline` the extra argument/return copies (`m00 <- m0`, `ec_result <- ...`), plumbing `if`s,
`inv` folded, `={arg}` shown as tuple projections were all seen on kem-dem.

**Changed:**
- **`clone ... with theory X <- Y` now exists** (`ecParser.mly` `clone_override`:
  `THEORY x=uqident mode y=uqident renames`); it works (`clone T as T2 with theory X <- A2.`
  compiles). §8.1 says there is no such override. Story 3's specialisation rationale stands but is
  no longer forced by the language.
- **`assert` and `class` are no longer keywords** in `ecLexer.mll` (`op assert : int.` compiles;
  `assert (true);` as a statement now says `unknown procedure: assert`). **New reserved words:**
  `raise exception idassign why3 subtype circuit` and the capitalised `Pr Self Top`; `global bind
  array ring field` are still usable as identifiers. Stories that generate `assert` statements
  should be checked against this.
- The opam binary reports `r2026.09-9-g884dad7`, one commit ahead of the clone.

## Deviations from §3

- Goal `id` is the 1-based ordinal, not the EasyCrypt goal handle (the type is abstract in
  `ecCoreGoal.mli`; exposing it would touch another file). It is not stable across commands.
- Extras beyond §3: goal-level `text` (the goal as `cli` prints it) and `tvars`; `stmt_pp` per
  side; `ident` tags; a `top`/`name` split of procedure paths (`EcPath.x_tostring` gives
  `Top.M./f`).
- Hoare/phoare/ehoare `S` judgements use `program` (a SIDE) where `equivS` has `left`/`right`.
  A side's locals are at `left.memtype.locals`, not `left.locals`.
- `text` is printed at the configured `PP:width`; every `pp` is single-line (margin 10^6), except
  statements, which keep their own newlines.
- Text-only (no children): `modty` hypotheses and quantifier binders, `abs_st` hypotheses.
- Files touched beyond the list in §4: `src/ecOptions.mli` (the `cli_option` record is exported),
  `src/ecTerminal.mli` (the new constructor). The tests are a standalone script,
  `tests/json/check.py`, not wired into `config/tests.config` (its runner only compiles `.ec`
  files); run `python3 tests/json/check.py [--bin ./ec.native]`.
- `-json` wins over `-emacs` if both are given.

## Open issues

- `-server` is declared as `"server"` (`ecOptions.ml:423`) but read as `"why3server"` (`:548`);
  not fixed, as instructed.
- Any output that EasyCrypt writes to stdout *before* the terminal is constructed would precede
  the redirect; none was observed (the banner is emitted through the terminal and lands in the
  first answer's `messages`).
- Code review (standards): no documented standards in the clone; findings were duplication between
  `jexpr` and `jform` and between the `jside*` helpers, and stringly-typed kind names. Not
  refactored. Spec review: the goal id and the text-only nodes above; `app.op` is `null` unless the
  head is a direct operator (an `inv` reached through a local is not recognisable by `op`).
