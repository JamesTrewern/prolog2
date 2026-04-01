# Prolog<sup>2</sup>

[Prolog<sup>2</sup>](https://link.springer.com/chapter/10.1007/978-3-032-09087-4_3) is a machine learning and logic programming framework, that implements native second-order logic and SLD resolution. This is an extension of Meta-Interpretive Learning, which was first used in 
[Meta-interpretive learning of higher-order dyadic datalog: predicate invention revisited](https://link.springer.com/article/10.1007/s10994-014-5471-y?fromPaywallRec=false)

This project aims to allow for more complex formations of second-order clauses and resolution.

# Defining second order clauses

Traditional meta-rules can be written simply by making predicate symbols start with upper case letters. 
We must define which variables will remain as variables when a new clause is created from this higher-order clause.
We define these existentially quantified variables using curly braces like so:  `{X,Y}` 

```prolog
P(X,Y):- Q(X,Y), {P,Q}. %Identity

P(X,Y):- Q(X,Z), R(Z,Y), {P,Q,R}. %Chain

P(X,Y):- Q(X,Z), P(Z,Y), {P,Q}. %Tail Recursion
```

By default Existentially quantified varibles inside the `{X,Y}` notation are contrained so they can't become the same value or unify.
This is intended to prevent unwanted recursion in meta-rules. If you want to remove this constraint EQ variables can be placed in `[]`

```prolog
P(X,Y):- Q(X,A), R(Y,B), {P,Q,R}, [A,B].
P(A,B), [A,B] % Meta fact
```

With this notation many we can create many interesting second-order clauses </br> 
for example, we can introduce certain constant predicate symbols either in the head or body to allow us to have greater control over the clauses that will be learnt.
We can also create second-order clauses with only constant predicate symbols but existentially and universally quantified variables to denote the introduction of some constants

``` prolog
p(X,Y):- Q(X), R(Y), {Q,R}.

P(X,Y):- q(X,Y), R(Y), {P,R}.

p(X,Y):- q(X,Z), {Z}. %matching with this clause will create a new clause where Z is a constant
```

This can even be extended to using infix operators in second-order clauses

``` prolog
P(X,Y):- X > Y, Q(Y), {P,Q}.

P(X,Y):- Z is X + Y, Q(Z), {P,Q}.
```

# Running Prolog<sup>2</sup>

```bash
#Inside the Prolog2 Repo
$ cargo run [CONFIG_FILE]
#Using the binary
$ prolog2 [CONFIG_FILE]
```

## Configuration Options
Configured in a JSON file (default: `setup.json`):
``` json
{
    "config" : {
        "max_depth": 20,
        "max_clause": 4,
        "max_pred": 2
    },

    "body_predicates" : ["dad/2","mum/2"],
    "examples" : {
        "pos" : ["ancestor(ken,james)", "ancestor(christine,james)"],
        "neg" : []
    },
    "files" : ["examples/simple_family.pl"],
    "auto" : true,
    "top_prog" : false,
    "reduce" : false,
    "approx_tolerance_pct" : 10
}
```
`config` is used by the solver, to limit the possible search size.<br>
`max_depth`: how many sub_goals deep the solver is allowed to go.<br>
`max_clause`: number of clauses that can be added to hypothesis.<br>
`max_pred`: number of invented predicates within the hypothesis.<br>

`examples`, `auto`, `top_prog`, and `reduce` are all optional fields.

`approx_tolerance_pct` sets the tolerance for the `=~=` (approximately-equal) operator. The value is an integer percentage — `10` means the two sides may differ by up to 10 % relative to the larger magnitude. Defaults to `10` if omitted. Can also be set programmatically via `App::approx_tolerance(pct)`.

If the config file includes an `examples` field, Prolog<sup>2</sup> will immediately attempt to prove the examples as a query and output any learned hypotheses. 
If `examples` is omitted, an interactive REPL is started where queries can be entered manually.

The `auto` option makes the program iterate through all possible proofs in a query. By default this is off and after each proof the program awaits user input (Space/;: continue, Enter: stop).

`files`: a list of either directory or file paths. If a directory is found it recursively searches subdirectories and loads all files with a .pl extension

# Top Program Construction

Prolog<sup>2</sup> supports Top Program Construction (TPC) as an alternative to the standard second order SLD-Resolution hypothesis search. TPC constructs the Top program — the set of clauses in all correct hypotheses — directly in polynomial time, then reduces it to remove redundant clauses using Plotkin's program reduction algorithm. This approach is based on the work of [Patsantzis and Muggleton (2021)](https://link.springer.com/article/10.1007/s10994-020-05945-w).

The TPC pipeline has three stages: **Generalise** searches each positive example in parallel to collect all constructible clauses, **Specialise** removes any clause that entails a negative example, and **Reduce** applies Plotkin's reduction to eliminate redundant clauses while preferring general patterns over specific ones.

To enable TPC, add `"top_prog": true` to your config file:<br>
The reduction step is turned off by default (useful for profiling or inspecting the raw top program), to include the reduction step add `"reduce": true` to the config.

``` json
{
    "config" : {
        "max_depth": 5,
        "max_clause": 2,
        "max_pred": 1
    },
    "body_predicates" : [
        "short/1",
        "closed/1",
        "long/1",
        "open_car/1",
        "has_car/2"
    ],
    "examples" : {
        "pos" : ["e(east1)", "e(east2)", "e(east3)", "e(east4)", "e(east5)"],
        "neg" : ["e(west6)", "e(west7)", "e(west8)", "e(west9)", "e(west10)"]
    },
    "top_prog" : true,
    "reduce" : true,
    "files" : ["examples/trains/trains.pl"]
}
```

Running this on Michalski's trains problem produces:

```
=== Reduced Program (2 clauses) ===
  e(Arg_0):-has_car(Arg_0,Arg_1),pred_1(Arg_1).
  pred_1(Arg_0):-short(Arg_0),closed(Arg_0).
```

# Step by Step Demonstration of New Clause Generation

1. First, we define a higher-order clause in our program
        `P(X,Y):-Q(X,Y), {X}`
2. Next, the prover reaches some goal that can match with the higher-order clause
        `p(a,b)`
3. This creates the binding 
        `{P/p, X/a, Y/b}`
4. From this binding a new goal is generated, Q becomes an unbound variable
        `_100(a,b)`
5. Then, as this is a higher order clause, a new 1st order clause is created from the binding. The universally quantified variable X does not bind to a, but instead it transitions to an existentially quantified variable</br>
`p(X,b):- _100(X,b) `
6. Finally as the new clause has an unbound variable we add a constraint to our unification rules saying that _100 can not be bound to the value p

# Example usage

## Family relations

first, we lay out our background knowledge.</br> 
What would have been called meta-rules is now better described as second-order clauses, where {P,Q} denotes that P and Q are variables which are existentially quantified, meaning they will become constants in new clauses derived from these meta rules. 

``` prolog

mum(tami,james).
mum(tami,luke).
mum(christine,tami).
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
dad(ken,kelly).
dad(adam,luke).

P(X,Y):-Q(X,Y), {P,Q}.
P(X,Y):-Q(X,Z),P(Z,Y), {P,Q}. % Tail Recursion
```

We must then define our learning parameters in a config file

``` json
{
    "config" : {
        "max_depth": 10,
        "max_clause": 4,
        "max_pred": 1,
        "debug": false
    },
    "body_predicates" : [
        "dad/2",
        "mum/2"
    ],
    "examples" : {
        "pos" : ["ancestor(ken,james)", "ancestor(christine,james)"],
        "neg" : []
    },
    "files" : ["examples/ancestor/family.pl"]
}
```

Then we can execute the binary with an argument for the path of the config file

```
$ target/debug/prolog2 examples/ancestor/config.json
TRUE
ancestor(Arg_1,Arg_2):-dad(Arg_1,Arg_4),ancestor(Arg_4,Arg_2).
ancestor(Arg_1,Arg_2):-dad(Arg_1,Arg_2).
ancestor(Arg_1,Arg_2):-mum(Arg_1,Arg_4),ancestor(Arg_4,Arg_2).
ancestor(Arg_1,Arg_2):-mum(Arg_1,Arg_2).

TRUE
ancestor(Arg_1,Arg_2):-pred_1(Arg_1,Arg_4),ancestor(Arg_4,Arg_2).
pred_1(Arg_1,Arg_2):-dad(Arg_1,Arg_2).
ancestor(Arg_1,Arg_2):-pred_1(Arg_1,Arg_2).
pred_1(Arg_1,Arg_2):-mum(Arg_1,Arg_2).

TRUE
ancestor(Arg_1,Arg_2):-pred_1(Arg_1,Arg_2).
pred_1(Arg_1,Arg_2):-ancestor(Arg_1,Arg_4),pred_1(Arg_4,Arg_2).
pred_1(Arg_1,Arg_2):-dad(Arg_1,Arg_2).
pred_1(Arg_1,Arg_2):-mum(Arg_1,Arg_2).

FALSE
```
## Map

``` prolog
map([],[], P).

map([H1|T1], [H2|T2], P):-
    P(H1,H2),
    map(T1,T2,P).

double(X,Y):-
    Y is X + X.
```

``` json
{
    "config" : {
        "max_depth": 10,
        "max_clause": 0,
        "max_pred": 0,
        "debug": false
    },
    "body_predicates" : ["double/2"],
    "files" : ["examples/map/learn_map_double.pl"]
}
```

```
$ prolog2 "examples/map/bind_double.json"
?- map([1,2],[2,4],double).
TRUE
FALSE
?- map([1,2],[2,4],X).
TRUE
X = double
FALSE
?- 
```


# Examples
- [ancestor](examples/ancestor/README.md)
- [parity](examples/parity/README.md)
- [map](examples/map/README.md)
- [odd_even](examples/odd_even/README.md)
- [robots](examples/robots/README.md)
- [trains](examples/trains/README.md)
