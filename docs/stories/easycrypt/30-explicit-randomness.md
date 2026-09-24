# Story 30 — Explicit randomness (documented, not scheduled)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Status:** **design record only. Do not implement until the owner schedules it.** This is the
"second approach" of `docs/easycrypt-interaction-and-branching.md`. The owner deferred it: *"Let's
skip approach 2 and the export it needs in the first implementation. Document the idea though."*
**Depends on:** 23, 27.

---

## 1. The problem

In lockstep execution (story 23), a sampling is only useful to EasyCrypt when both sides reach
their paired samplings **at the same time**. Otherwise it is a **stuck point** and the proof admits
it. Domino itself has no such restriction: its randomness is an eager function
`rand(sample id, counter)`, and the randomness mapping relates draws wherever they occur.

The idea is to export games whose randomness is **drawn up front by the router** and consumed by the
packages. The proof then:

1. separates all sampling from the rest of the oracle with one `seq`;
2. discharges that `seq` with the randomness mapping as its postcondition;
3. runs lockstep on sampling-free code, where no sampling can be stuck.

The owner wants it exposed as `domino debug --easycrypt --explicit-randomness`, and the export
needs the same flag (`domino easycrypt --explicit-randomness`), since it changes the generated
game.

## 2. The first proposal, and why it was rejected

The first proposal was to pass each oracle a `rand` tuple argument and let each package forward its
callees' shares. **Rejected by the owner:** a package does not know how it is composed, so it cannot
know how much randomness its dependencies need.

## 3. The two designs on record

### 3.1 A shared sampler package

- One package per game exposes `Get(PackageInstance, Oracle, SampleId)` and
  `Set(PackageInstance, Oracle, SampleId, Counter, Value)`.
- Every sampling in every package becomes a call to `Get` with its own identity.
- The router samples all values at the start of each oracle call and stores them with `Set`.
  Alternatively, the sampler draws lazily when the router asks it to.
- Every package instance must be initialised with an **identifier** (a string or integer) so that
  it can name itself in `Get`.

### 3.2 Per-package sample tables (the owner's "simpler approach")

- Each package keeps, for each sample id in each of its oracles, a table `T : (int, bits) fmap` and
  a counter. A sampling becomes `x <- T.[ctr]; ctr <- ctr + 1`.
- Each package exposes one extra oracle to the router, which resets its counters to zero and
  installs its tables.
- The router draws every value for an oracle call up front, **as many per sample id as the bound
  `sample_max_counter_extractor` computes after `loopunroll`**, and installs them before calling
  the package. Drawing values a given path never uses is sound, because sampling a `Bits`
  distribution is lossless. It also matches Domino's eager semantics.

This design keeps packages ignorant of composition, which was the flaw in §2: each package only
knows its own sample ids.

## 4. The proof shape either design enables

- `seq k k : (#pre /\ <randomness mapping as equalities between the drawn values>)`, where `k`
  covers the router's draws. Discharge it with `auto`, or with `rnd` plus a bijection when the
  mapping permutes components.
- **The mapping must still be evaluated by the solver, not read** (story 23 §3.3). Where it
  depends on state or arguments, the `seq` postcondition is the mapping's premise implying the
  equality.
- The rest of the oracle is sampling-free, so lockstep proceeds with branches only. A branch that
  doesn't synchronize is split (`if{1}`, then `if{2}`), exactly as in story 23.

## 5. Open questions for when it is scheduled

- **Which design:** 3.1 needs instance identifiers and one sampler per game; 3.2 needs one extra
  oracle per package. Which reads better in the generated code?
- **Faithfulness:** the exported game differs from the plain export. Is Domino's eager semantics
  enough justification, or is an EasyCrypt lemma relating the two exports (lazy vs. eager sampling)
  wanted?
- The adversary's view is unchanged, since the router's exported signatures stay the same. Verify
  this against the game interface (story 04).
