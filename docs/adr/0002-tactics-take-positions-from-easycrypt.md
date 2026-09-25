# Generated tactics take positions and names from EasyCrypt; lockstep supplies only decisions

**Status:** accepted. Implemented by `docs/stories/easycrypt/26-easycrypt-session-and-alignment.md`
and `27-tactic-generation.md`.

Domino generates EasyCrypt tactics by walking a **lockstep execution** of an oracle pair and turning
each joint decision (synchronized branch, split, paired or independent sampling, stuck point) into
a proof step. The lockstep execution runs on story 08's lowering, which has the same order and
nesting as the program EasyCrypt shows after `proc; inline.` but a **different statement list**.
EasyCrypt's `inline` adds an argument copy per parameter and a return copy at every call through
an import adapter and at the entry call. It also renames locals by its own scheme (`r` becomes
`r6`, `ec_result_2` becomes `ec_result3`). So a statement count or a variable name taken from our
listing is wrong in EasyCrypt, and it can change whenever EasyCrypt's inliner does.

We therefore split the responsibilities. **Lockstep decides *what* to do; EasyCrypt's own view of
the goal, read as JSON from a live session, decides *where* and *with which names*.** Straight-line
code is consumed with bare `sp`. Branches are addressed by code-position patterns (`^if`), or by
counts computed from EasyCrypt's statement list. A sampling's variable names come from EasyCrypt's
`<$` statement. The two views are tied together by **alignment of decision skeletons**, meaning
branches, samplings and ends with every assignment ignored. That is the only property of EasyCrypt's
inliner we depend on, and EasyCrypt cannot change it without changing the program's meaning.

## Considered options

- **Make the lowering reproduce EasyCrypt's `inline` statement for statement**, so counts and names
  from our listing are right. Rejected: it copies an implementation detail of EasyCrypt into
  Domino, and every EasyCrypt release that changes the copies or the renaming silently breaks every
  generated proof. It also pushes EasyCrypt-only statements into the debugger's listing, which the
  standalone debugger has no use for.
- **Recognise EasyCrypt constructs by name** (`ec_done`, `ec_r<N>`, `abort_flag`) in the goal text
  and handle them with fixed tactics. Rejected: it is text pattern matching on EasyCrypt's output,
  which is what the JSON interface exists to avoid, and the names are EasyCrypt's renamings, not
  ours.
- **Drive everything by trial in EasyCrypt**, with no lockstep: try `rcondt`/`rcondf`, then `if`,
  then `if{1}`, as `docs/BranchingAlgorithm.pdf` does by hand. Rejected as the *primary* strategy,
  because it cannot relate samplings (the PDF's own open question) or tell a hopeless branch from
  a provable one. Kept as the **fallback** at a mismatch, so one unexpected EasyCrypt statement
  costs one trial search, not an admit.

## Consequences

- Tactic generation needs a live EasyCrypt with `cli -json`
  (`25-easycrypt-json-cli.md`). The standalone debugger (`domino easycrypt --debug`, which was
  `domino debug --easycrypt` until ADR 0003) does not.
- Alignment runs at the start of every oracle's translation, and is exposed on its own as
  `domino easycrypt --check-alignment`. Its acceptance bar is zero mismatches across the testing
  ladder, 4WHS included, so a mismatch at translation time is a regression, not an expected event.
