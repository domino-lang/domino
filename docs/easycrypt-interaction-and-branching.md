We are finally approaching generating partial proofs in EasyCrypt using the 
symbolic execution. So the idea is that the symbolic execution helps us 
to figure out how to do the branchings in EasyCrypt proof of equivalence.

# Standalone symbolci execution on EasyCrypt code
The idea is to do symbolic execution on EasyCrypt code with the style we do in Domino 
but story 16 and 17 already create EasyCrypt ready code that is type checkable in Domino.
Any way the easycrypt debugging shoudl be targeted for easyCrypt debugging and it may use 
the output of story 16 and 17 or directly EasyCrypt IR lowering!

## first approach
Unlike domino debugger which explores both left oracle first and then moves to the right 
oracle, I want to execute both sides at the same time until I hit a branching/decision point 
such as if condition. There I want to check whether both conditions are synchronized and equivalent, that is 
if I enter both branches at the same time or I go to the else branches in both.
If the branches are not equivalent, the algortihm considers all four cases on decision point on left 
and right and try to prove all cases!
Another possibility other than a branchign point is randomness sampling. Since we 
are aiming the symbolci execution to be useful for EasyCrypt proof export, we want to hit synchronized 
randomness samplings on both sides at the same time. If we don't, we admit that case in EasyCrypt as it needs more attentions. When using the 
debugger in EasyCrypt mode, we note it that down where we get stuch (in html report so user can 
conenct it to EasyCrypt admits) and continue Domino-style debugging which does the randomness smapling with just a function call and assuem Domino randomness mapping! Essentially the domino debugger in EasyCrypt mode 
should help the user connect whether the admit cases are verified in Domino or they are also inconlusive there 
as well. 

## second approach
Since EasyCrypt stops at sampling operations so the user maps the left sampling 
to right one ad we want to avoid this to significantly help the user. In order to
mimic domino, we move the sampling operations to the top level game router module (the one
that holds abort_flag state) and we sample all the randomness needed in the oracle there.
How do we know what samplings are needed? For each oracle, the randomness the oracle 
needs has to be explicit as part of its arguments. Then the router module 
knows what values of what types need to be sampled and it will sample them. 
All the explicit randomness can be a tuple rand that each oracle parses in EasyCrypt. 
In the proof generation, since all the sampling are in the beginning, we use the seq 
tactic and separate the piece of code in the beginning with all the samplings 
from the rest of the code which is sampling-free. Domino randomness mapping should help 
us to discharge that but otherwise, we use Domino randomness as the post condition for 
the seq which allows us to use the mapped values in the rest of the oracle code. 
We can then do the synchronized branching as in first approach that we do in Domino
without admitting the randomness samplings that are not synchrinized in left and right.
When the branching does not match, we go left first and then right first.
I want this approach to be exposed as domino debug --easycrypt --explicit-randomness

# Interaction with EasyCrypt
The challenge here that we also saw from Story 15 is that we need to be able to parse EasyCrypt context and remainign goals and the goal types to be able to see whether we should use another heuristic in translation or 
the translated proof went through. Also if heuristics fail, we just put admit and delegate it to the user.
EasyCrypt has an -llm option but we want to possibly see if a sea in EasyCrypt code is needed to be able to properly access the proof goals and context at any given point in the proof. This for sure 
benefits from a live EasyCrypt session that can undo or go further so it is fast!

# Active EasyCrypt proof generation using symbolic execution and interaction with EasyCrypt
The main goal of symbolic execution explained above is to interact with easycyrpt 
and help with active translation! So when we do the branching and we notice that 
two if conditions are synchronized we can use the "if" tactic with trivial introduction pattern "if => //"
to discharge the condition equivalence goal and then easycyrpt considers two goals for the if and else case.
We use sp to consume a bunch of assignments. When a piece of code does not have branching 
we can just use auto => /#. When we have to branch only on one side we can the one-sided branchign tactics liek "if {1}".

However, it is useful on its own as well so 
I want to be able to call it on its own to get the artificats we get at the moment.
Note that the debugger now works for one oracle and claim at a time. For easycrypt-mode debugging, 
we also focus on one oracle at a time but we need to show two claims at each branch
equal-output (i.e. same-output + equal-abort so without assuming no-abort) and invariant
and indicate it in the artifcas we generate includign html report.

Summary:

Domino debugger in Easycrypt mode oeprating on EasyCrypt code attempts a synchronized 
execution on both sides and tracks how much code it consumes to reach every decision point on left and 
right. If it hits a decsion point only on left or right or the decion points are not equivalent, 
it considers all four cases and uses smt in the debugger to see which ones it actually goes 
in and continue execution there. IF we hit a randomness only on one side we admit there for now!

Domino debugger in EasyCrytpt mode but explicit randomness option is more faithful 
with explicit randomness.

Interaction with Easycrypt by extendign easycrypt to access proof goals
and context and in machine readable format provided by Easycyrpt in a live session
to not waste time on reproving things.

## Postponed:

### Proving Lemmata in Domino as equiv lemmata in Easycrypt

### Prove equivalence of each oracle separately and then using conseq!