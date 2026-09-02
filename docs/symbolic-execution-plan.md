I want to create a proof debugger with the idea of symbolic execution. 
At the moment we translate oracles after some transformations (mainly returnify
and treeify) to pure SMT/LIB functions with ite and let statements 
(returnify makes sure there is a return end of the 
function and treeify makes sure that each if is followed by an else to be translated 
to ite which adds a lot of branches). 
Then the next important part is the claims we prove. 
We prove these claims by assuming invariants on the old state and assuming all the other dependent claims (if state relations, on the new state, if lemmata both on old and new). 
The symbolic execution debugger should be exposed as a cli 
option say debug that accepts proofs, proofsteps and oracles
and even claims. For the selected oracle, it symbolically excutes the left oracle until each return or abort point (abort, assertion and unwrap). By symbolically, I want it 
to build an execution tree and for each execution path from beginning of the oracle, it compiles if/else conditions (for branches it opens), it compiles the conditions and for each assignment, it uses dynamic single assignment where a fresh variable version is used for assignments to the same variable. Note that the initial conditions are invariants on the old game states and dependencies of a claim. Upon an assertion or unwrap, one branch is that assertion fails which the return value would be abort or the value is none which again the return value aborts. When it hits an abort or return, one symbolic execution path of the left oracle is finished and the return value of the oracle and the new state of the game should be properly stored in the variable
that the claim dependencies expect so the encoding makes sense. With the left oracle finishes, the fun debugging part, starts by symbolically executing the right oracle with all the path conditions and initial conditions (invariants, lemmata i.e. claim depenendencies). However, this time whenver it hits a branching point (if/else, unwrap or assertion) it queries the solver for which branch it should take. if the solver gives unsat for one of the conditions, that should not be reachable and the other branch should be chosen. If the solver gives sat or unknown, that branch is a possible path and should be continured to be executed symbollically. When the right oracle also hits an abort or return (a termination point), then the actual goal of the claim is checked. IF it fails (i.e. sat or unknown), we can give precise possible execution path causing the error.
I want to optionally (CLI) be able to do these interactive solver checks for the left oracle meaning, a solver is called for each branching point, and it would be checked with the invariants and claim dependencies which branch should be taken. Again, if a branch gives, unknown or sat, that should be explored. Only an unsat branch can be skipped.
I want to optionally disable the solver checks for the right 
oracle. Thereofore, if disabled, all possible branches on the right are also explored and the only solver checks is the claim assertion when the right oracle also terminates (hits abort or return)

For interactive interaction with solver use cvc5-rs crate which is cvc5 bindings for rust!

Note that whenever I mention invariants, I mean all package, game, and main invariant.

For all sat answers of the solver for claim assertion (when both oracles have temrinated and we are checking the claim),
I want a model to be generated.

I want full log of path conditions and complete incremental transcript passed to solver. I also want it to be properly organzied, so I can see all the execution paths on the left and execution paths on the right induces by the path on the left. It could be visualized in a tree through html to be explored? It should be also logged to file. You can use the inlining feature on branch amir/ty-params-features, to assign id's or names to if/else conditions, assertions, unwraps, returns, aborts in the full inlined code, so you can refer to denote the execution path chosen on the left and under that list the explored viable paths on the right.