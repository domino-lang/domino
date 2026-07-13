I want to extend Domino language so that I can define invariants, randomness mappings,
and lemmata and other proof components directly in theorem files instead of in 
SMT-LIB language in a separate file. This document illustrates these new components 
and suggested syntax.

# Assumptions over theorem constants
It is very often needed to assume some relations over theorem constants. Therefore, 
I want a new `constraints` spec among other theorem specs as follows:
```
const h: Int;
const d: Int;
..
constraints {
    d > 0 and h > d
}
```
The whole block accepts one expression and it is the same as Domino expressions.

# Equivalence specifications
Currently, the user provides the list of SMT files that contain their lemmata,
randomness mappings, and invariants as `invariant : [path1 path2 ...]` for each 
oracle. However, the user should provide only one set of invariants for the entire
equivalence hop but different randomness mappings and lemmata for each of the oracles.

## Invariants
There are two concepts for invariants here:
- invariant body as a logical predicate (currently defined in SMT-LIB)
- how the same invariant is proved in each oracle (currently defined in Domino language 
in the theorem file with the list of dependencies)

We just want to bring invariant body definition to Domino and want to be as
flexible as the current design on how invariants could be proved in each oracle.
We often define invariants as logical AND of several predicates and 
we use SMT-LIB functions with `define-fun` to organize invariants. These SMT-LIB
functions usually have names that illustrate the purpose of the invariant. 
However, during debugging, it is very useful to know exactly which of the ANDed 
invariants is/are failing. Therefore, we allow the user to name their invariants 
and we automatically AND them when assuming invariants for the old game states but 
discharge sub claims for each named invariant to be proved on the new game states.
This way, we can report to the user which invariant is exactly failing and which 
can be proved. It is very useful if these sub claims of the invariant claim 
can be parallelized. We get back to this later on.

The new syntax allows the user to define their named invariants in invariant blocks
in the equivalence level as follows:
```
invariant InvariantName {
    Expr
}
```

Currently, invariant functions in SMT-LIB take two arguments: states of the left 
and right hand sides of the equivalence. As in the SMT Rewrite feature, the new 
syntax allow the user to access game and package states without the need for arguments 
and selectors.

```
left.PackageInstanceName.Field
right.PackageInstanceName.Field
```

Additionally, I want `let` expressions in Domino. (also in invariant blocks)

The syntax is as follows: 
```
let x <- a in Expr
or
let (x, y, z) <- (a, b, c) in Expr
```

which binds x, y, z to a, b, c respectively in Expr. This directly translates 
to let expressions in SMT-LIB.

Additionally, the user can refer to theorem constants in the invariants using 
the syntax `const.ConstantName`.

When proving claims for each oracle, we allow two syntaxes and semantics for 
verifying invariants. The first one is as follows which looks like the current 
syntax. However, when translating to SMT, we generate a function called `invariants`
which ANDs all the user provided invariants (here Invariant1 and Invariant2) and 
then in the claim we want to prove, for each of the invariants we check if 
`(=> (invariants old-left old-right) (Invariant1 new-left new-right))` and 
`(=> (invariants old-left old-right) (Invariant2 new-left new-right))`. Note that 
we assume randomness mappings and whatnot but they are not mentioned for simplicity.

```
(define-fun invariants
    (
        (left ...)
        (right ...)
    )
    Bool
    (and
        (<invariant-Invariant1> left right)
        (<invariant-Invariant2> left right)
        ...
    )
)
```

Syntax1:
```
equivalence Game1 Game2 {
    invariant Invariant1 {
        Expr
    }
    invariant Invariant2 {
        Expr
    }
    ...
    Oracle1: {
        claims: {
            invariant: [no-abort]
            ...
        }
    }
}
```

Syntax2: (explained in the next section on proving by case)
```
equivalence Game1 Game2 {
    invariant Invariant1 {
        Expr
    }
    invariant Invariant2 {
        Expr
    }
    ...
    Oracle1: {
        claims: {
            invariant requires [no-abort, ...] by split {
                Invariant1: [...]
                Invariant2: [...]
            }
            ...
        }
    }
}
```

### Proving initial state
It is very helpful to know exactly which invariant may not hold in the initial 
state.

Syntax:
```
equivalence Game1 Game2 {
    invariant Invariant1 {
        Expr
    }
    invariant Invariant2 {
        Expr
    }
    claims: {
        invariant-in-initial-state : []
    }
    ...
}
```

```
equivalence Game1 Game2 {
    invariant Invariant1 {
        Expr
    }
    invariant Invariant2 {
        Expr
    }
    claims: {
        invariant-in-initial-state {
            Invariant1: [...]
            Invariant2: [...]
        }
    }
    ...
}
```

## Proving by cases
*This is a feature inspired by Yao Hybrid Security case study*

A new syntax allows to prove any claim (invariant, Invariant1, same-output, 
equal-aborts, and user defined lemmata) by cases:
```
Invariant1 requires [no-abort, ...] by cases {
    case1: [...]
    case2: [...]
    ...
}
```
where case1, case2 are lemma names (explained bellow) or invariant expressions
and some shared lemmata can be required for all cases.

Other examples:
```
invariant requires [no-abort, ...] by cases {
    case1: [...]
    case2: [...]
    ...
}
```

Other examples:
```
same-output requires [no-abort, ...] by cases {
    case1: [...]
    case2: [lemma1]
    ...
}
```

We generate the following sub claims to verify a "claim by cases":
1. We check whether cases are comprehensive: We take the logical OR of the cases 
and check whether invariants (on old state) and randomness mappings together imply
ORed cases. That is, we verify 
```
(=> 
    (and (invariants old-states) randomness-mapping required-lemmata) 
    (or case1 case2 ...)
)
```
2. We check each of the cases: For example for case1 and lemma same-output to be proved
```
(=> 
    (and (invariants old-states) randomness-mapping case1 other-lemmata-in-case required-lemmata) 
    same-output
)
```

### Question
1. Should we have a block for each case if the user has some lemmata to be proved 
for each case? For example,
```
same-output requires [no-abort, ...] by cases {
    case1 requires [lemma1, lemma2] {
        lemma1: [lemma2]
        lemma2: []
    }
    case2: [lemma3]
    ...
}
```
Note that this is helpful as lemma1 and lemma2 shall be proved only in case1 and not 
generally!

2. Should we allow nested "by cases", i.e. lemma2 can also be proved with "by cases" again?

3. When the user wants to prove a case with a lemma, if they are not admitting the 
lemma, should we allow them to mark lemmata to be proved only in this specific case 
and not generally? For example, they can put a `*` before or after the lemma name.

## Randomness Mappings
Currently, the user can define only two randomness mappings in Domino lang:
`randomness: simple` and `randomness: none`.

For each oracle, the user should define a randomness mapping predicate as follows:
```
randomness {
    Expr
}
```
Randomness mapping is a special predicate that does not required arguments.

The expression supports the following convenient selectors:
```
left.id -> left sample id
right.id -> right sample id
left.ctr -> left counter/offset
right.ctr -> right counter/offset
args.OracleArgument -> Oracle argument
const.ConstantName
left.state.PackageInstanceName.FieldName -> translate to old state in SMT
right.state.PackageInstanceName.FieldName -> translate to old state in SMT
```

User can refer to a sampling id as `left.PackageInstanceName.OracleName.sample-name`
or `right.PackageInstanceName.OracleName.sample-name`. Then with type checking 
we make sure left.id is asserted to value of left game sample id's.

*Arguments and theorem constants are inspired by Yao Hybrid Security case study and states by Yao Layer Security*

*We add injective-randomness as a claim in each oracle*

Syntax:
```
equivalence Game1 Game2 {
    Oracle1: {
        randomness {
            Expr
        }
        claims: {
            injective-randomness: []
        }
    }
}
```

### Question
1. Do we need to allow the user to access new states and return values of the oracles?
2. Currently, `randomness: simple` asserts mapping of zero offsets with the same 
ids. How about having `randomness: all` for mapping of all offsets?

## Lemmata
User can define equivalence-wide or oracle-specific lemmata.

### Rules

*Lemmata can be invoked in other lemmata.*

*Scoping rules apply. Lemmata in an oracle can only be used in that oracle 
while lemmata defined in the equivalence can be used everywhere.*

### Equivalence-wide
```
equivalence Game1 Game2 {
    lemma LemmaName {
        Expr
    }
    ...
}
```

The expression supports the following convenient selectors for equivalence-wide lemmata:
```
const.ConstantName
left.state.old.PackageInstanceName.FieldName
left.state.new.PackageInstanceName.FieldName 
right.state.old.PackageInstanceName.FieldName
right.state.new.PackageInstanceName.FieldName
```

### Oracle-specific
```
equivalence Game1 Game2 {
    Oracle1 {
        lemma LemmaName {
            Expr
        }
        ...
    }

}
```

The expression supports the following convenient selectors for oracle-specific lemmata:
```
args.OracleArgument -> Oracle argument
const.ConstantName
left.output -> Oracle output
right.output -> Oracle output
left.state.old.PackageInstanceName.FieldName
left.state.new.PackageInstanceName.FieldName 
right.state.old.PackageInstanceName.FieldName
right.state.new.PackageInstanceName.FieldName
```

## Predicates
User can define equivalence-wide or oracle-specific predicates.

*Predicates can be invoked in other predicates, lemmata, invariants, and functions.*

*Equivalence-wide Predicates that use new states can not be used in invariants.*

### Equivalence-wide
Argument-free:
```
equivalence Game1 Game2 {
    predicate Pred {
        Expr
    }
    ...
}
```

With Arguments:
```
equivalence Game1 Game2 {
    predicate Pred(x: Table(Int, Int), y: Maybe(Int)) {
        Expr
    }
    ...
}
```

The expression supports the following convenient selectors for equivalence-wide predicates:
```
const.ConstantName
left.state.old.PackageInstanceName.FieldName
left.state.new.PackageInstanceName.FieldName 
right.state.old.PackageInstanceName.FieldName
right.state.new.PackageInstanceName.FieldName
```

### Oracle-specific
Argument-free:
```
equivalence Game1 Game2 {
    Oracle1 {
        predicate Pred {
            Expr
        }
    }

    ...
}
```

With Arguments:
```
equivalence Game1 Game2 {
    predicate Pred(x: Table(Int, Int), y: Maybe(Int)) {
        Expr
    }
    ...
}
```

The expression supports the following convenient selectors for oracle-specific predicates:
```
args.OracleArgument -> Oracle argument
const.ConstantName
left.output -> Oracle output
right.output -> Oracle output
left.state.old.PackageInstanceName.FieldName
left.state.new.PackageInstanceName.FieldName 
right.state.old.PackageInstanceName.FieldName
right.state.new.PackageInstanceName.FieldName
```

## Functions
User can define equivalence-wide or oracle-specific functions.

Similar to above. Syntax:

```
equivalence Game1 Game2 {
    function Func(x: Table(Int, Int), y: Maybe(Int)) -> Int {
        Expr
    }
    ...
}
```

### Question
Do we have any example that is nicer with a function that does not return Bool (i.e. not predicates)

# Questions
1. Should we allow standard Domino language instead of expressions in invariants,
lemmata, predicates, functions, and randomness mappings. Then, we might not need 
let expressions. We could by Rust style that the last expression is returned 
and is type checked to be Boolean (except for functions). Also, we can allow return 
statements. These might make randomness mappings or invariants more readable :D 
2. Should we allow passing game and packages as arguments to functions or predicates?
3. Do we need to share predicates and functions among game hops?