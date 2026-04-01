# Odd / Even

This learning task demonstrates the need for negative examples to specialise the hypothesis.
It also demonstrates the power of mutual recursion and predicate invention as odd and even 
rely on one another for their definition and the odd predicate must be invented.

## Background Knowledge

<!-- embed-start: odd_even.pl -->
```prolog
zero(0).
prev(1,0).
prev(2,1).
prev(3,2).
prev(4,3).

P(X):- Q(X), {P,Q}.
P(X):- Q(X,Y), R(Y), {P,Q,R}.
```
<!-- embed-end: odd_even.pl -->

## Configuration

<!-- embed-start: config.json -->
```json
{
    "config" : {
        "max_depth": 6,
        "max_clause": 3,
        "max_pred": 1,
        "debug": false
    },
    "body_predicates" : [
        "zero/1",
        "prev/2"
    ],
    "examples" : {
        "pos" : ["even(4)"],
        "neg" : ["even(3)"]
    },
    "files" : ["examples/odd_even/odd_even.pl"]
}
```
<!-- embed-end: config.json -->

## Expected Hypotheses

**Hypothesis 1**
```prolog
even(Arg_0):-prev(Arg_0,Arg_1),pred_1(Arg_1).
pred_1(Arg_0):-prev(Arg_0,Arg_1),even(Arg_1).
pred_1(Arg_0):-prev(Arg_0,Arg_1),zero(Arg_1).
```

**Hypothesis 2**
```prolog
even(Arg_0):-prev(Arg_0,Arg_1),pred_1(Arg_1).
pred_1(Arg_0):-prev(Arg_0,Arg_1),even(Arg_1).
even(Arg_0):-zero(Arg_0).
```
