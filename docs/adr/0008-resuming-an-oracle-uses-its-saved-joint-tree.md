# Resuming an oracle uses its saved joint tree, not a deterministic debugger

**Status:** accepted. Implemented by
`docs/stories/easycrypt/resume-an-oracle-from-its-saved-joint-tree.md`. Extends ADR 0006 (which
resumes whole oracles only).

Story 37 resumes an equivalence one oracle at a time. An oracle left `interrupted` is proved again
from the start, lockstep execution included, and a kem-dem or 4WHS oracle can take many minutes.
To resume *inside* an oracle, the next proof job has to walk the same joint tree the stopped one
walked: the session record names its work by joint node (`N<k>`), and a node id means nothing
against a different tree.

Running lockstep execution again does not reliably give back the same tree. Any `unknown` from
cvc5 (a wall-clock `tlimit-per`, when one is set, a different cvc5 version, or a change in what the
engine sends) turns into a stuck point, which gives the tree a different shape and different node
ids. Nobody has audited the engine for iteration order that could leak into the tree either.

We **save the tree** instead. When lockstep execution finishes, before the first sentence is sent,
the proof job writes `Eq_<L>_<R>.<oracle>.tree.json` beside the session record. That file holds
the lockstep outcome, its summary, and a **fingerprint** of everything lockstep execution read for
this oracle: the monomorphic code of every instance reachable from the oracle in both games, the
game constants, the randomness mapping, and the state relation, invariant and lemma SMT files. The
domino version is not part of it. A resuming job loads the tree and does not run lockstep
execution.

When the fingerprint no longer matches the project, the job **warns and carries on with the saved
tree**. Such a mismatch can only arise when the project changed *without* exporting again, because
`export --force` deletes records and trees together. In that case the EasyCrypt files on disk are
as old as the tree (ADR 0006: `prove` never translates), so the saved tree fits the proof being
built better than a fresh one would.

## Considered options

- **Make lockstep execution deterministic** (`rlimit-per` in place of `tlimit-per`, a fixed seed,
  `BTreeMap` everywhere) **and run it again on resume.** Rejected. It changes the solver's limits
  from seconds to resource units. It still breaks across cvc5 versions. And it pays for lockstep
  execution again on every resume. Determinism stays desirable in its own
  right, but resume no longer depends on it.
- **Resume at the last accepted sentence** by recording every attempt and its answer, then
  replaying the walk against that log. Rejected for now. The walk's position inside a node is a
  Rust call stack, not data. Replaying it needs a layer under `Session` and an append-only attempt
  log, while a node costs minutes at most to prove again.
- **Fall back to a fresh lockstep execution when the fingerprint does not match.** Rejected: it
  builds a tree for code the EasyCrypt files do not contain.
- **Read the tree back from the debug folder's `trace.json`.** Rejected: that folder holds run
  artifacts, which every run regenerates and may overwrite without asking. Losing the tree must not
  be that cheap.

## Consequences

- The saved tree is protected like the session record (ADR 0004). `export --force` deletes it, and
  `prove --force` (or `--resume restart`) replaces it.
- A record written before this story has no saved tree. Its `interrupted` oracles are proved again
  from scratch, with a warning.
- Nothing re-checks a stale tree against the EasyCrypt goals beyond the alignment report that
  every run writes anyway. A stale tree whose skeleton no longer matches shows up there as
  mismatches, and its admits are the price.
- The solver options of lockstep execution do not change.
