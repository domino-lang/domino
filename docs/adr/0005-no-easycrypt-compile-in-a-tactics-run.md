# A tactics run does not compile the file it writes

**Status:** accepted. Revises `docs/stories/easycrypt/27-tactic-generation.md` §3.7.

Story 27 ended each equivalence by running `easycrypt compile` over the rewritten `Eq_*.ec`, and on
failure recompiled each oracle alone and rewrote the guilty ones as a bare `admit`, reporting `BUG`.
The gate never fired on any project of the testing ladder. We have removed it from the run.

Two reasons. The first is that it checks little: every sentence in the file was accepted by a live
EasyCrypt session moments earlier, so the file failing as a whole would mean a defect in how
`Script::render` rebuilds bullets and indentation from a depth counter — a Domino bug, which is why
story 27 labelled it `BUG` rather than a disagreement. The second is decisive: the gate's recovery
path **rewrites the file with fewer proofs than were proved**, which directly contradicts the
property a tactics run now guarantees — that the file on disk holds what has been proved so far.
A mechanism whose failure mode is discarding proved work cannot sit in a pipeline whose point is
never to discard proved work.

`compile` itself stays, called by the two tests that already use it, so a render defect is still
caught in CI rather than in a user's run.

## Considered options

- **Keep one compile per equivalence but only report the failure, never revert.** The closest call:
  it costs seconds against a run of minutes and keeps the only automated detector of a render bug.
  Rejected on the grounds that nothing in the pipeline should be able to report a proof as
  suspect when no evidence says the proof is wrong; the tests cover the defect it looks for.
- **Replace it with a structural self-check** (rendered bullet count against goals closed).
  Rejected as unnecessary once the tests carry the property.

## Consequences

- Nothing in a tactics run checks the written file as a whole. A future reader finding no compile
  step will assume it was forgotten; this ADR exists to stop them from putting it back without
  reading the second reason above.
- `OracleTactics::reverted` and the report's `BUG:` line go away with it.
- Incremental writes — per oracle or per joint node — are therefore cheap, which is what makes
  writing after every node affordable at all.
