# Parity

Here we attempt to learn the edges of a finite state machine by passing an input list and expected final state.<br>
We define the possible states with a `q` fact, and the initial state with `q0`.<br>
The recursive control mechanism of the FSM is all in first order logic (standard prolog), however the `edge` predicate is defined with a single meta-clause.
In the edge meta-clause we use the `q` predicate to allow for the introduction of constants but they do not add any information in the final hypothesis, which could essentially be reduced to a set of 4 facts.<br>
The `Q1` and `Q2` constants can't be part of the standard Existentially Quantified set as by default this prevents the introduced constants from having the same value, which is an important step for limiting unwanted recursion in meta-clauses, so we define them as constants in an Existentially Quantified List `[Q1,Q2]` which does not have the same constraints.

## Background Knowledge

<!-- embed-start: parity.pl -->
```prolog
fsm(Input,Result):-
    q0(Q0),
    fsm(Input,Q0,Result).

fsm([],State,State).
fsm([H|T],Q1,State):-
    edge(H,Q1,Q2),
    fsm(T,Q2,State).

edge(El,Q1,Q2):-
    q(Q1),
    q(Q2),
    {El},[Q1,Q2].

q0(even).
q(even).
q(odd).
```
<!-- embed-end: parity.pl -->

## Configuration

<!-- embed-start: config.json -->
```json
{
    "config" : {
        "max_depth": 10,
        "max_clause": 4,
        "max_pred": 0,
        "debug": false
    },
    "body_predicates" : [
        "add/3"
    ],
    "examples" : {
        "pos" : ["fsm([0,0,0],even)","fsm([1,0,0],odd)","fsm([0,1,0],odd)","fsm([1,1,0],even)"],
        "neg" : ["fsm([0,0,0],odd)","fsm([1,0,0],even)","fsm([0,1,0],even)","fsm([1,1,0],odd)"]
    },
    "files" : ["examples/parity/parity.pl"]
}
```
<!-- embed-end: config.json -->

## Expected Hypothesis

```prolog
edge(0,even,even):-q(even),q(even).
edge(1,even,odd):-q(even),q(odd).
edge(0,odd,odd):-q(odd),q(odd).
edge(1,odd,even):-q(odd),q(even).
```