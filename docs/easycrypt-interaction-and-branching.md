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
If the branches are not equivalent, the algortihm falls back from there to 
execution on the left until it terminates and then execution on the right.
Another possibility other than a branchign point is randomness sampling. Since we 
are aiming the symbolci execution to be useful for EasyCrypt proof export, we want to hit synchronized 
randomness samplings on both sides at the same time. If we don't we admit that case in EasyCrypt and 
in debugger, we note it that down and continue Domino-style debugging which does the randomness smapling with just a function call.

## second approach
Since EasyCrypt stops at sampling operations so the user maps the left sampling 
to right one ad we want to avoid this to significantly help the user

# Interaction with EasyCrypt

# Active EasyCrypt proof generation using symbolic execution and interaction with EasyCrypt
The main goal of symbolic execution explained above is to interact with easycyrpt 
and help with active translation! However, it is useful on its own as well so 
I want to be able to call it on its own to get the artificats we get at the moment.
Note that the debugger now works for one oracle and claim at a time. For easycrypt-mode debugging, 
we also focus on one oracle at a time but we need to show two claims at each branch
equal-output (i.e. same-output + equal-abort so without assuming no-abort) and invariant
and indicate it in the artifcas we generate includign html report.