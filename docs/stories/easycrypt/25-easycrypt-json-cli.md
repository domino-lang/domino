# Story 25 — `easycrypt cli -json`: machine-readable goals from a live session

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first (§3 "EasyCrypt
interaction", §8.1b).
**Repository:** the EasyCrypt clone at `easycrypt/`, which is its own git repository. **Branch
`amir/domino-easycrypt-integration`**, created from the clone's current head
(`r2026.09-8-g1e2d06ec`). Nothing in this story is committed to Domino, except this story's
implementation report under `docs/stories/easycrypt/`.
**Depends on:** nothing. It runs in parallel with 22–24.
**Blocks:** 26, 27.

---

## 1. Why this story exists

Tactic generation (story 27) has to know, after every tactic, which goals remain and what they look
like: their kind, hypotheses, programs, pre/post, quantifier binders and conjunct structure.
Parsing EasyCrypt's pretty-printed text is exactly what the owner wants to avoid, and it is lossy:

- `-emacs` mode prints only the first goal;
- `Goals:printall` prints the rest *without* hypotheses;
- the only JSON EasyCrypt writes (`.eco`, `compile -trace`) stores goals as strings;
- `llm -upto` is batch-only and re-checks the file on every call.

EasyCrypt already has what a live driver needs apart from structured output:

- an interactive loop with O(1) `undo N.`;
- SIGINT interruption;
- `yojson`, already linked (`src/dune:19`).

This story adds the structured output as a small, upstreamable patch.

## 2. Facts from the source (design session; verify against the branch)

- **Modes.** `src/ecOptions.ml:373-410` defines `compile`, `cli` (`-emacs`), `llm`
  (`-lastgoals`, `-upto`), `config`, `runtest`, `why3config`, `docgen`. `cli_option` is at
  `:32-35` and `:390-393`. The terminal is selected at `src/ec.ml:516-519`, and the interactive
  loop is `src/ec.ml:758-931`.
- **Terminals.** `src/ecTerminal.ml` has the emacs class (prompt `:72`, notices `:53-63`, errors
  `:87-97`) and the tty class (`:117-133`). The prompt `[<uuid>|<mode>]>` marks the end of a
  command's output.
- **Undo.** `src/ecCommands.ml:1041-1082`: the uuid is the undo depth. A success pushes one level
  (`print`/`search`/`locate` too); failures and pragmas don't. `pragma reset`/`restart` exist.
- **Goals.** `EcScope.xgoal` → `proof_uc` → `puc_active = Some (proof_auc, _)` →
  `puc_jdg = PSCheck proof`. The open goals come from `EcCoreGoal.opened`/`all_opened`
  (`ecCoreGoal.mli:199-205`). `pregoal = { g_uid; g_hyps : LDecl.hyps; g_concl : form; … }`.
  `LDecl.tohyps` gives `h_local : (EcIdent.t * local_kind) list`, where `local_kind` is
  `LD_var | LD_mem | LD_modty | LD_hyp | LD_abs_st` (`ecBaseLogic.ml:7-18`).
- **Formulas** (`ecAst.mli:173-201`), `f_node`:
  - ambient: `Fquant | Fif | Fmatch | Flet | Fint | Flocal | Fpvar | Fglob | Fop | Fapp | Ftuple
    | Fproj`;
  - program logic: `FhoareF/S | FbdHoareF/S | FeHoareF/S | FequivF/S | FeagerF | Fpr`;
  - `equivS = { es_ml; es_mr; es_pr; es_sl; es_sr; es_po }`;
  - instructions (`:106-114`): `Sasgn | Srnd | Scall | Sif | Swhile | Smatch | Sraise |
    Sabstract`;
  - memories: `memenv = memory * memtype`, with locals in `lmt_decl`.
- **Printers** (`src/ecPrinting.ml`): `PPGoal.pre_pp_hyp` (`:3402-3453`) assigns display names;
  `pp_goal1` (`:3455`) dispatches per kind; `pp_equivS` is at `:3322`. The public API is
  `EcCorePrinting.PrinterAPI`. `PPEnv.push_mem` is **not** exported, so the serializer must live
  in `ecPrinting.ml`.
- There is no generic visitor or deriving support, so the serializer is hand-written.
- Unrelated bug seen: `-server` is declared as `"server"` (`ecOptions.ml:423`) but read as
  `"why3server"` (`:548`). Note it in the report; don't fix it here.

## 3. Work to do

### 3.1 `cli -json`

A new flag on `cli`, and a new terminal class `from_json` in `ecTerminal.ml`. The input protocol
is unchanged: sentences on stdin, `undo N.`, `exit.`. For **every** processed sentence, write
**exactly one line** of JSON to stdout, and nothing else on stdout:

```json
{"version": "domino-json/1",
 "state": 7,                          // undo depth after the command
 "status": "ok" | "error" | "interrupted",
 "error": {"loc": {"start": 12, "end": 20}, "msg": "…"},   // only on error
 "messages": [{"level": "warning", "text": "…"}],
 "proof": null | {"goals": [ GOAL, … ]}}                   // ALL open goals, in order
```

Each `GOAL` is `{"id": …, "hyps": [HYP…], "concl": FORM}`. Each `HYP` is `{"name": …, "kind":
"var"|"mem"|"modty"|"hyp"|"abs_st", …}`: a type, a memtype or a formula, depending on `kind`.
Names are the ones `pre_pp_hyp` would display, so that a name used in a tactic is valid.

### 3.2 Full trees

Every node carries its kind, its children and a `pp` string: its own EasyCrypt text, printed in
the right memory context.

- **Formulas:** every `f_node` constructor. Quantifiers carry `binders: [{name, type}]` and the
  quantifier kind. `Fapp`/`Fop` carry the operator path, so `Domino_rel_keys` and `inv` are
  recognisable, plus type arguments. Program-logic judgements carry structured parts:
  `{kind: "equivS", left: {mem, locals, stmt}, right: {…}, pre: FORM, post: FORM}`, and likewise
  for hoare, phoare (with `cmp`/`bd`), ehoare, and the `F` (procedure-level) forms with procedure
  paths.
- **Statements:** a list of instruction nodes (`asgn`, `rnd`, `call`, `if`, `while`, `match`,
  `raise`, `abstract`), each with its `pp`. An `if`'s blocks and a `while`'s body are nested; an
  `asgn`/`rnd` has its lvalue (variables with their `pp`) and expression.
- **Expressions and types:** structured too, with `pp`.
- Paths (`EcPath`) are serialized as their printed qualified name. Identifiers are name plus tag,
  so two binders with the same name stay distinct.

Put the serializer beside `PPGoal` in `ecPrinting.ml`, and expose it through `PrinterAPI` as
`goal_to_json`. The design session estimated ≈400–550 lines of OCaml for the terminal and a hybrid
serializer; full trees will be more. Record the actual size.

### 3.3 Documentation and tests

- `doc/json-output.md` in the clone: the format, versioned. Domino's reader (story 26) is written
  against this document.
- Tests in EasyCrypt's own test setup, which cover:
  - a pRHL goal after `proc; inline.` with nested `if` and `<$`;
  - a goal with `forall` binders;
  - an error with location;
  - `undo` restoring an earlier state's exact goals;
  - multiple open goals, each with its own hypotheses.
- **Re-verify overview §8.1's EasyCrypt facts on this build** (they were established on r2026.06),
  and record any that changed.

## 4. Acceptance criteria

- [ ] Feeding a generated kem-dem `Eq_*.ec` sentence by sentence to `easycrypt cli -json -I <dir>`
      yields one JSON line per sentence, and the JSON parses with a standard parser.
- [ ] After `proc; inline.` on `PKENC`, the JSON has both programs as instruction trees whose
      `if`/`rnd` structure matches the text EasyCrypt prints, plus `pre`/`post` as trees. `post`
      shows `inv` as an operator application.
- [ ] After a tactic that leaves several goals, **all** of them are present, each with
      hypotheses.
- [ ] A `forall` goal lists its binders with names and types.
- [ ] `undo N.` returns the JSON of state `N` exactly.
- [ ] Without `-json`, EasyCrypt's behaviour is unchanged (its own test suite passes).
- [ ] The patch touches only `ecOptions.ml`, `ec.ml`, `ecTerminal.ml`, `ecPrinting.ml`,
      `ecCorePrinting.ml`, tests and docs. Anything else is justified in the report.

## 5. How to verify

```bash
cd easycrypt && git switch -c amir/domino-easycrypt-integration
make                              # or: dune build; see INSTALL.md
cd /tmp/ec-test && cp -r <kem-dem _build/easycrypt/…>/* .     # run outside the clone (§8.1b)
printf 'require import AllCore.\nlemma t (x : int) : forall y, x + y = y + x.\nproof.\n' \
  | <clone>/_build/default/src/ec.exe cli -json
```

## 6. Notes / risks

- Keep **one JSON line per sentence, and nothing else on stdout**. Notices, progress and prover
  chatter must go into `messages` or stderr, never onto stdout lines of their own. Domino relies
  on this framing.
- Large goals: 4WHS `inv` record literals are hundreds of lines. Don't truncate. Story 28 decides
  what to embed.
- Write it upstreamably: no Domino-specific names in the code, only in the version string.

## 7. State handed to the next story

Record in `docs/stories/easycrypt/25-…-IMPLEMENTATION-REPORT.md`:

- the branch and commit;
- how to build it;
- the binary path to use as `DOMINO_EASYCRYPT`;
- the format version;
- a sample JSON line for a pRHL goal;
- the §8.1 re-verification results;
- anything that deviates from §3.
