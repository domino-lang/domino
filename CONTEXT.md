# Context

The shared vocabulary of this repository. Glossary only — no implementation details, no plans.
When a term here conflicts with how a document or a piece of code uses a word, this file wins.

## Domino core

**Package** — a reusable unit of stateful code: parameters, state fields, imported oracle
signatures and oracle definitions. A package is a *template*; it is never used directly.

**Package parameter** — a value a package is instantiated with. Three kinds: booleans
(see *idealization bit*), integers, and functions.

**Package instance** — a package with all of its parameters bound, living inside one composition
under an instance name. By the time a proof runs, an instance's code has been rewritten so that
every parameter and type is substituted: an instance is *monomorphic*.

**Composition** (also **game**) — a set of package instances plus the call graph wiring them
together, and the list of oracles it exports to the adversary. The call graph is **acyclic**, and an
oracle cannot call another oracle of its own package, so a call can never re-enter the package it
came from. Package instances do **not** share state: an oracle can only write its own instance's
state fields. (The SMT encoding collects all of a game's state into one datatype; that is an
encoding convenience, not shared ownership.)

**Game instance** — a composition with its game constants bound, named in a theorem. Several game
instances can share one composition and differ only in the constants they bind.

**Theorem constant** — a value declared at theorem level and passed down into game instances and
from there into package instances. Boolean, integer or function.

**Oracle** — a procedure a package defines. An **exported oracle** is one the composition offers
to the adversary.

**Continuation** — the statements that follow a given statement in the same block, together with
everything that follows the blocks enclosing it. What a mid-body abort or return skips.

**Abort** — an oracle ending without a value: an explicit `abort`, an `assert` whose condition is
false, or unwrapping a `None`. An abort is not an error; it is a run of the game in which the
adversary loses its ability to query further. Abort **cascades**: a caller whose callee aborted
aborts too, and once a game has aborted no later query does anything.

**Idealization bit** — a boolean parameter that selects between a real and an idealized behaviour
of a package. Related instances usually differ only in these bits.

**Equivalence** — a proof step claiming two game instances are perfectly indistinguishable. Its
obligations are discharged per exported oracle.

**Claim** — one obligation of an equivalence for one oracle: `invariant`, `same-output` or
`equal-aborts`, each with its dependencies.

**State relation** — a predicate over the left and right game states, hand-written in SMT-LIB, that
an equivalence maintains. One set of state relations per equivalence.

**Randomness mapping** — a per-oracle predicate, hand-written in SMT-LIB or chosen by name, that
says which left sampling draws the same value as which right sampling. It may depend on the state
and the oracle's arguments, so whether two particular samplings are paired is a question for the
solver, not something read off the mapping's text.

## Debugging

**Strategy** — how the debugger walks two oracles: *sequential exploration* or *lockstep
execution*. Independent of the **listing** it walks them on.

**Listing** — the code the debugger executes and labels: the Domino code, or the EasyCrypt code the
export produces. `domino debug` walks the Domino listing; the EasyCrypt listing is reached through
`domino easycrypt`.

**Sequential exploration** — the strategy that takes every path of the left oracle, then, under
each, every path of the right oracle.

**Lockstep execution** — the strategy in which both oracles advance together, each over its
straight-line code up to its next *decision point*, and the two decision points are then resolved
jointly. It is what an EasyCrypt pRHL proof does, which is why it exists.
_Avoid_: synchronized execution (the word *synchronized* is reserved for the outcomes below).

**All-claim run** — a debugger run that names no claim and therefore checks the oracle's whole
obligation set — its proof tree plus the generated package and game invariant claims — on one
shared exploration.
_Avoid_: claim-free run, full-obligation run.

**Unreachable** — a verdict meaning a claim was not refuted because the situation it was checked in
cannot arise *under the assumptions in force*. Either the path pair itself is infeasible, or the
pair happens but this one claim's dependency is false on it. It is never a synonym for *verified*:
telling the two apart is what stops an all-green run from being mistaken for a proof.

**Decision point** — where one side of a lockstep execution cannot continue as straight-line
code: a branch, a sampling, or the end of the oracle.

**Synchronized branch** — both sides at a branch whose conditions are equivalent under the path
condition and the assumptions, so both take *then* or both take *else*. A branch that is not
synchronized is **split**: every combination of the two sides' outcomes is considered, and the
infeasible ones are pruned. A branch on one side only is always split.

**Synchronized sampling** — both sides at a sampling that the randomness mapping, under the path
condition, forces to draw equal values. A sampling the mapping relates to nothing on the other side
is an **independent sampling** and is consumed on its side alone.

**Stuck point** — a place on a joint path where lockstep execution cannot hand EasyCrypt a proof
step: a paired sampling reached on one side before its partner, or a sampling whose pairing the
solver cannot decide under the path condition. The proof admits it; the execution carries on past
it with Domino's randomness semantics, so the paths below still get verdicts.

**Joint path** — one path of a lockstep execution: the sequence of joint decisions from the start
of both oracles to a pair of terminals.

**Plumbing branch** — a branch that exists in the EasyCrypt code only because EasyCrypt allows one
exit point: a *done flag* guard, the guard on an inlined call's result, or the router's abort-flag
guard. It decides nothing Domino would call a decision, but an EasyCrypt proof has to step over it
like any other branch.

**Decision skeleton** — a program with its straight-line code erased: the tree of its branches,
samplings and ends. Two programs that differ only in assignments have the same skeleton.

**Alignment** — matching the decision skeleton EasyCrypt shows for an oracle with the one lockstep
execution walks, so that each EasyCrypt proof step can be tied to a joint decision. Where the two
disagree there is a **mismatch**.

**Equal-output** — the claim, checked in EasyCrypt mode, that both oracles produce the same result
where an abort counts as a result: *same-output* and *equal-aborts* together, with *no-abort* not
assumed. It is EasyCrypt's `={res}` on an optional result, and is never declared in a project.

## EasyCrypt export

**Package variant** — one EasyCrypt module generated for a package, specialised to a distinct
assignment of the parameters that are baked into its code: the integers used as *Bits* widths and
the function parameters. Two package instances that agree on those share one variant. Boolean and
value-integer parameters do not distinguish variants (they are initialization arguments), and
neither does *how an instance is wired* — a package's variant is a fact about the package, never
about the composition it appears in.

**Import interface** — the module type a package declares for the oracles it expects, named by the
package's *own* import names. It lives with the package, so a package never refers to the interface
of whatever happens to serve it.

**Import adapter** — a module belonging to one composition that satisfies one package instance's
import interface by forwarding each expected oracle to the instance that provides it. It exists
because a package may import from several instances at once, and because a composition may rename
an oracle on the way in. It holds no state and is generated only when a single instance cannot
serve the interface as it stands.

**Instance clone** — an EasyCrypt theory clone of a package variant, one per package instance, so
that each instance has its own memory. Instances of the same variant differ only by their clone.

**Router** — the EasyCrypt module generated for a composition. It owns the *abort flag*, exposes the
composition's exported oracles, and forwards each to the package instance that defines it. Packages
themselves carry no abort flag.

**Abort flag** — the router's single piece of state, recording that the game has aborted. It is the
EasyCrypt counterpart of Domino's abort cascade: while it is set, every oracle returns `None`.

**Done flag** — a *per-oracle local*, distinct from the router's abort flag, recording that this
oracle has already aborted or returned. EasyCrypt allows only one exit point, so an oracle's
continuation cannot be skipped by returning early; it is skipped by being guarded on this flag
instead. An oracle whose continuation is never at risk carries no done flag.

**Experiment** — the EasyCrypt module that initializes a router with a game instance's constants and
runs the adversary against it. One per composition; the constants are its `run` arguments.

**Game interface** — the EasyCrypt module type listing the oracles a router exposes to the
adversary. Compositions exporting the same signatures share one.

**Game-state record** — a flat record type collecting one game instance's package state fields plus
its abort flag. It exists solely so that invariant operators take a single argument per side; no
router or package ever uses it.

**`Domino_` operator** — an EasyCrypt operator translated from a hand-written SMT-LIB state relation
or helper function, named after its SMT original.

**Tactics run** — one translation of a theorem's equivalences into EasyCrypt proofs against a live
EasyCrypt. Its defining property: the proof files on disk always hold what has been proved so far,
so stopping it early costs no proved oracle.

**Seal** — to close every goal an oracle still has open with `admit`, so the oracle's proof is
complete as written even though the walk had not finished it. Sealing is what makes a stopped
tactics run leave a usable file. It works on a copy of the script and sends nothing to
EasyCrypt; its admits carry the reason `interrupted`.

**Partial proof** — a proof file holding proved bullets alongside the admits of a seal. It is a
proof EasyCrypt accepts, not a draft.

**Run artifact** — a file a tactics run writes *about itself* rather than as translation output:
the live page, the EasyCrypt transcript, the per-equivalence report, the alignment report, the
debug output of lockstep execution. Regenerated every run and never hand-edited, so unlike
translation output it may be overwritten without asking.

**EasyCrypt transcript** — the record of one tactics run's exchange with EasyCrypt: every sentence
sent, in order, with EasyCrypt's answer and how long it took. Undone attempts and the `undo`
sentences themselves are part of it. By default each answer's goals are **capped** to what the live
page shows (`--ec-transcript full` keeps them verbatim); records are only ever appended, never
compacted, because the page reads them back by byte offset. _Distinguish_: the **solver transcript** is the raw incremental
exchange with cvc5, a debugging aid for the debugger itself.
