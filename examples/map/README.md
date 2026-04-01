# Map
This example aims to show the advantages of a native second-order SLD-resolution engine.
A map predicate can be defined in prolog using the call functionality, however by natively allowing goals to have variable predicates the syntax is much more natural. It also allows us to pass a variable predicate to map which can then be bound.
## Prolog<sup>2</sup> Code
<!-- embed-start: map.pl -->
```prolog
map([],[], X).

map([H1|T1], [H2|T2], P):-
    P(H1,H2),
    map(T1, T2, P).

double(X,Y):-
    Y is X + X.
```
<!-- embed-end: map.pl -->

## Config
<!-- embed-start: config.json -->
```json
{
    "config" : {
        "max_depth": 5,
        "max_clause": 0,
        "max_pred": 0,
        "debug": false
    },
    "body_predicates" : [
        "double/2"
    ],
    "files" : ["examples/map/map.pl"]
}
```
<!-- embed-end: config.json -->

## Queries
```
?- map([1,2,3],[2,4,6],double).
TRUE
?- map([1,2,3],[2,4,6],X).
TRUE
X = double
```

# Learn Map Double
Here we expand upon the map example by Defining a meta-clause version of the map predicate. 
We are also able to define a meta-fact for the base case.

## Background Knowledge

<!-- embed-start: learn_map_double.pl -->
```prolog
Map([],[], X), {Map}.

Map([H1|T1], [H2|T2], P):-
    P(H1,H2),
    Map(T1, T2, P),
    {Map, P}.

P(X,Y):-Q(X,X,Y),{P,Q}.

add(X,Y,Z):- Z is X + Y.
```
<!-- embed-end: learn_map_double.pl -->

## Configuration

<!-- embed-start: learn_config.json -->
```json
{
    "config" : {
        "max_depth": 5,
        "max_clause": 3,
        "max_pred": 1,
        "debug": false
    },
    "body_predicates" : [
        "add/3"
    ],
    "examples" : {
        "pos" : ["map_double([1,2,3],[2,4,6],double)"],
        "neg" : []
    },
    "files" : ["examples/map/learn_map_double.pl"]
}
```
<!-- embed-end: learn_config.json -->

## Expected Hypothesis

```prolog
map_double([Arg_0|Arg_1],[Arg_2|Arg_3],double):-double(Arg_0,Arg_2),map_double(Arg_1,Arg_3,double).
double(Arg_0,Arg_1):-add(Arg_0,Arg_0,Arg_1).
map_double([],[],Arg_0).
```
