# Ancestor

This is a classic MIL example which aims to demostrate the power of predicate invention and recursion.
The goal is to find a definition of an ancestor using tail recursion and an invented parent predicate

## Background Knowledge

<!-- embed-start: family.pl -->
```prolog
mum(tami,james).
mum(tami,luke).
mum(lil,adam).
mum(lil,kelly).
mum(lil,saul).
mum(christine,tami).
dad(jim,ken).
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
dad(ken,kelly).
dad(chris,tami).
dad(adam,luke).

P(X,Y):-Q(X,Y), {P,Q}.
P(X,Y):-Q(X,Z),P(Z,Y), {P,Q}. % Tail Recursion
```
<!-- embed-end: family.pl -->

## Configuration

<!-- embed-start: config.json -->
```json
{
    "config": {
        "max_depth": 10,
        "max_clause": 4,
        "max_pred": 1,
        "debug": false
    },
    "body_predicates": [
        "dad/2",
        "mum/2"
    ],
    "examples": {
        "pos": [
            "ancestor(ken,james)",
            "ancestor(christine,james)"
        ],
        "neg": []
    },
    "files": [
        "examples/ancestor/family.pl"
    ]
}
```
<!-- embed-end: config.json -->

## Expected Hypotheses

**Hypothesis 1**
```prolog
ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).
ancestor(Arg_0,Arg_1):-dad(Arg_0,Arg_1).
ancestor(Arg_0,Arg_1):-mum(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).
ancestor(Arg_0,Arg_1):-mum(Arg_0,Arg_1).
```

**Hypothesis 2** *(with invented predicate)*
```prolog
ancestor(Arg_0,Arg_1):-pred_1(Arg_0,Arg_2),ancestor(Arg_2,Arg_1).
ancestor(Arg_0,Arg_1):-pred_1(Arg_0,Arg_1).
pred_1(Arg_0,Arg_1):-dad(Arg_0,Arg_1).
pred_1(Arg_0,Arg_1):-mum(Arg_0,Arg_1).
```