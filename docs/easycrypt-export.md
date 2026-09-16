# EasyCrypt Export
This document describes the feature of exporting Domino packages, games, and 
theorems, and proofs to EasyCrypt.

Exporting to EasyCrypt requires several steps. First, we need to translate 
Domino objects into EasyCrypt language. In the next step, we can translate the 
code equivalence hops up to branchings using the symbolic execution debugger 
branching foundation. However, sometimes EasyCrypt can not prove the goals that 
SMT solver can discharge for Domino and they need more care.

There is manual translation of Domino 4WHS project to EasyCrypt in /Research/ec4whs
repo. The 4WHS project that is translated exists under the subdirectory /Research/ec4whs/4WHS and there 
are two translation is subdirectories /Research/ec4whs/simple and /Research/ec4whs/full.
Only get inspiration for the rough idea of translation that is explained in details here. 
Do not generate and code specific to that project. That is just an example of a translation 
and the following algorithm and explanation is superior to that and also differs from place 
to place. For example that project defines custom types with named fields but Domino does not 
support record types with named fields and the corresponding type is a tuple. In the automatic translation
we of course generate a tuple as we don't know logical names for the fields.

## Translating packages and games and theorems
Each package in Domino can be translated to a module in EasyCrypt. Package state 
are module variables. A package might import oracles from other packages and 
these dependencies are module parameters that module can call. Module parameters 
in EasyCrypt need to be module type so we each package we need to create a module 
type that lists the oracles of the package. Packages also have parameters in Domino
that are initialized by game parameters (also called constants) which are in 
turn initialized by theorem parameters (also called constants). There is no direct 
translation of that to EasyCrypt. For that, notice that we have the following types of 
package parameters.
1) Booleans (idealization bits)
2) Integers
3) Functions

Booleans can go to the module state. Integers can also go to module state 
unless they are used as type parameters for Bits(n). These integers are exclusively 
for types and are not used in the code. Since these integers are essentially template for types,
we need to gather all Bits types in the Domino theorems (i.e. for identifiers Bits(n) and 
literals Bits(256)) and generate a separate module for the same package but with a different 
Bits type hardcoded wherever it is used. Domino source code already extracts all types 
for each theorem. For functions, we can define operators once and share it 
among all modules we generate. 

### Domino Types
In Domino we have the following types that should be mapped to the corresponding 
types mentioned below:

| Domino | EasyCrypt 
| - | - |
| Integer | int |
| Maybe | option |
| Table | fmap |
| Bool | bool |
| Bits(n) | custom type bits_n |
| Bits(256) | custom type bits_256 |
| Tuples | tuples in easycrypt constructed with * |
| Fn | Operator |

Tuple items do not have names in Domino similar to EasyCrypt. Domino extracts all 
theorem integer parameters n1, n2, etc that Bits is used with them and then 
generates sorts Bits_n1, Bits_n2 in the SMT. We want the same semantics in EasyCrypt, 
where we generate custom types Bits_n1, Bits_n2 , etc. This is also true for literals. 
So a separate type for Bits_256 and Bits_512. No further property is known for this type
and no relations need to be generated for them. We also have Bits(*) in Domino that 
can be translated to type `bits` (without suffix). For each of these types, we 
generate two constant literals as 0_n and 1_n or 0_256 and 1_256 in Domino. 
In EasyCrypt, We can generate two constants zero_n and one_n (or zero_256 and one_256) for each 
identifier and literal that domino has extracted.

All the functions and types can be placed in a Types.ec file and imported into other files 
we generate for each package and game and gamehop.

### Package initialization
Each package needs an init procedure in EasyCrypt that allows initializing its state. You can see 
the initial values in Domino source code and use those. 

### Package language and semantics
Domino and EasyCrypt language are very close but still different.
First of all, there is no need to care about loops and translating them at the moment.
We unroll bounded loops in Domino and we can translate to EasyCrypt after that transformation in Domino. 
If the code still has loops (should be only unbounded loops after transformation), we can just give 
error that we do not support loop translation now.
The key difference is the abort semantics and return statements.

Oracles can abort mid execution in Domino and the rest of code is not executed 
but there is no such concept in EasyCrypt. This is also similar to SMT translation 
so things can be reused. The idea is that when an oracle returns a type T in Domino, 
then in EasyCrypt we return option T where None value corresponds to Abort and some 
value corresponds to the actual value domino oracle returns. So when oracle aborts we return none otherwise we return Some.
If the Domino oracle return type is empty, so the oracle does not return with a value, 
we can translate that to option bool where we return None for abort and return true for 
all return points. There are three possible cases that we abort in Domino:
1. abort statement
2. Unwrap(value) if value is None
3. assert expr if expr = False
For each of these cases we want to return None rightaway and stop execution of that oracle.
However, EasyCrypt does not allow returning in the middle of oracle. One can only have one 
return in the end of oracle. On the other hand, Domino allows early return statement.
To deal with early return, we need extra conditioning and additional else branches 
to make it a pure function. The treeify transformation in Domino exactly does that because 
the SMT define-fun also has similar restriction to EasyCrypt. (No return in the middle)
The abort behaviour also cascades so when we call an oracle and that oracle returns None,
the caller oracle also aborts. When any oracle aborts, the abort semantics requires 
that no further queries to oracles should be possible. To solve this issue, we need 
an abort flag in the state of the module and wrapping the body of modules with 
an if condition that executes the body when the flag is false and otherwise returns None.
In game translation, we explain how to avoid having abort flag in all modules 
corresponding to packages but rather in one router module for each game/composition. 
Moreover, the same router module exposes the game interface and an init procedure 
that calls init on all instantiated packages of the game. If a package is stateless 
and it does not have any boolean or non-Bits integer parameters, then it may not have 
an init procedure.

It's also easier to wrap all variables in a package state into a record type in EasyCrypt.
These record types can be defined in Types.ec as well. 

### Games (or compositions)
Each game in Domino instantiates some packages (even several instances of the same 
package) with concrete values or game parameters. It also describes the call graph 
of packages and how they are composed. The idea is to have one module for each 
game that exposes all the oracles the game exposes and just proxy calls the package
but wrapped in the abort_flag if condition. So this game module has a state variables bit
for abort_flag and only calls the proxied packages when it is false. Moreover, it 
exposes an init procedure that calls the init of all instantiated packages either 
with concrete parameters or the game parameters. the game parameters are the 
arguments to the init procedure and it initializes the parameters and state of all packages.
The only remaining part is how to compose packages and instantiate several instances of the 
same package in EasyCrypt. EasyCrypt allows cloning modules which makes the cloned 
module have a separate memory than the original one. As a result, we need to clone 
modules of our packages for each package instance with the name in Domino (note that 
modules names need to start with capital letter and this is not restricted for package instance 
names in Domino so package instance cloned modules can be prefixed with Pkg.).
The game module then needs to call the correct cloned modules with 
correct module parameters (according to the graph) at the call site.
So all the cloning of modules and the game module should exist in the same file. 
We want cloned modules to be local so we can have the same package instance names in other 
games. 
Additionally for each game, we need a game interface module type 
that lists the oracles exported to the adversary (except the init). We also need 
an experiment module with name "Exp_{GameName}" that exposes a run function 
that takes game parameters as arguments and call the initialization function of the game 
module with the parameters and then calls the run function of an adversary (which is just an abstract module
that is parameterized by the game interface and exposes a single run function).
See the ec4whs project as an example. The difference in this translation is that 
experiment is game specific but in ec4whs, it is parameterized by a game.
The pattern we follow is that the adversary is parameterized by a game interface 
and for all games with the same interface we can share a game interface. The games can indicate that they implement 
the game interface. You can put all game and package interfaces in Interfaces.ec file.
The game module's only state is abort_flag which is a bool.

## Translating invariants
For each code equivalence, we have one set of invariants. Invariants are defined 
using (define-state-relation invariant) macro and helper functions. All helper functions 
can be translated as they are to EasyCrypt operators because there are matching types 
and logical operators between SMT and EasyCrypt. See ec4whs as an example. 
For state relations, you can define operators again in EasyCrypt but we don't have 
the game states as types. For convenience, we can define a record type for each 
game that contains the package states based on the instance name. 
Here record fields could be prefixed with "pkg_". Then the invariant function can 
expect a game state type for the left and the right and looking ahead, when 
writing code equivalence proofs and using the call tactic, we can call the invariant operator 
with the game states built and passed as arguments to operators. The game states 
are just helper types and should not be used in game module. 

The only difference between the generated EasyCrypt invariant and Domino invariant 
is that we need to relate the idealization bits (package parameters stored in state)
and also state that Domino invariants should hold only abort_flag is false. (Invariant 
are allowed to not hold when abort_flag is true. 
You can see one example of how this is expressed in ec4whs/full/Invariants.ec)
For idealization bits (package parameters), it's better to relate them in a separate operator which is called by the 
invariant operator to make it cleaner. Note that the invariants about package 
parameters and how they are related can be extracted from how packages are initialized and compositions in Domino. 
That is, which packages use the same game parameter and how the games are instantiated in the theorem file. 
For the bits that are initialized with concrete value, we can also directly express them.
Moreover, they always hold regardless abort flag. So the translated invariant 
in EasyCrypt is op invariant (left : Game_left_state) (right : Game_right_state) = package_parameters_invariant left right /\ 
left.game_module.abort_flag = right.game_module.abort_flag /\
!left.game_module.abort_flag => Domino_invariant left right. 
(I am not putting the arguments.. THis is a sketch.)
And all Domino state relations and helper functions can be translated to operators with prefix "Domino_"

## Translating code equivalence proofs
We need a directory per theorem and for each theorem we have a list of game hops. 
For each code equivalence, we have a file with the name Eq_{LeftGameInstanceName}_{RightGameInstanceName}.ec
that contains the lemma and its proof
and Eq_{LeftGameInstanceName}_{RightGameInstanceName}_Invariants.ec that contains 
invariant definitions.
The adversary module type and memory restriction happens in Eq_{LeftGameInstanceName}_{RightGameInstanceName}.ec.
Again look at ec4whs examples simple and full to see how equivalence file begins.
We need a lemma stating that probabilities that the experiment modules defined 
in game module files when ran given the adversary (note that our experiments 
unlike ec4whs do not get the game as parameter but just the adversary)
is equal. 

The proof begins with the byequiv and the call tactic to provide the invariants and the last first 
to prove the induction-start and we use 
auto => />.
smt(map_empty emptyE).

then proving the invariant for each oracle begins in the order of how they are listed in the 
game interface module type given to the adversary. 

I am not expecting you to generate a full proof deterministically and automatically.
The point is these EasyCrypt proofs have a lot of boiler plate branching code that 
needs to be written and are relatively automatizable. We have ran experiments that 
apparently, it has close relation with the branches that the symbolic debugger finds. 
So I want you to generate these branching code and then put admit in the interesting parts.
For this we need to run the symbolic debugger on EasyCrypt like code. 
So we need proper internal AST representation of inlined code of these games 
and packages we translated to EasyCrypt. Note that I don't want to do symbolic debugging 
for arbitrary EasyCrypt code. It is for a treeified Domino code which has the abort_flag condition 
when the game module is inlined. So a key step is that you create proper data strucutres 
for the easycrypt and do not quickly genenrate EasyCrypt as text so the symbolic debugger can be extended to 
run on this ast. 

Note that running debugger takes time and it makes sense to be a second command 
so the translation can be done quickly and for equivalence proof you put "admit." right at 
the point of beginning to generate branching code for oracles.
Note that debugger UI should inline the generated Easycrypt code to really help a user 
working on the EasyCrypt to match the proof and remaining admits to the EasyCrypt code. 
Domino syntax should be forgotten at this point.

In this first version, let's just run the debugger on the EasyCrypt code we have in our 
datastrucutres and display the user the verified and pruned paths as we do now but just on inlined easycrypt code we generate instead of inlined Domino code.

## Translating randomness mappings
We do not translate randomness mappings at the moment.

## Translating reductions
Let's skip translating reductions for now!

The file structure of the generated EasyCrypt project could look like a Domino project.
A directory for all packages. A directory for all the games and a directory for all theorems. 

You need to look into EasyCrypt source code and documentation (available as 
submodule in ec4whs repo) as well as 4WHS manual translation case studies 
in ec4whs/simple and ec4whs/full to make sure the easycrypt code you generate is correct and compiles.
EasyCrypt is installed on this system.