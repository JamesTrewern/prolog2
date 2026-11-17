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

With this notation we can create many interesting second-order clauses </br> 
for example, we can introduce certain constant predicate symbols either in the head or body to allow us to have greater control over the clauses that will be learnt.
We can also create second-order clauses with only constant predicate symbols but existentially and universally quantified variables to denote the introduction of some constants

``` prolog
p(X,Y):- Q(X), R(Y), {Q,R}. % Meta-Clause with constant head predicate

P(X,Y):- q(X,Y), R(Y), {P,R}. % Meta-Clause with constant body predicate

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
        "max_clause": 4
    },

    "body_predicates" : ["dad/2","mum/2"],
    "examples" : {
        "pos" : ["ancestor(ken,james)", "ancestor(christine,james)"],
        "neg" : []
    },
    "files" : ["examples/simple_family.pl"],
    "auto" : true,
    "approx_tolerance_pct" : 10
}
```
`config` is used by the solver, to limit the possible search size.<br>
`max_depth`: how many sub_goals deep the solver is allowed to go.<br>
`max_clause`: number of clauses that can be added to hypothesis. This also bounds predicate invention, which has no setting of its own: an invented predicate needs a clause defining it on top of the clause that calls it, so a hypothesis can hold at most `max_clause - 1` invented predicates.<br>

`examples`, `auto`, `parallel`, and `approx_tolerance_pct` are all optional fields. Any other key is an error rather than being ignored, so a typo or a field name from an older version is reported instead of silently taking its default.

`approx_tolerance_pct` sets the tolerance for the `=~=` (approximately-equal) operator. The value is an integer percentage — `10` means the two sides may differ by up to 10 % relative to the larger magnitude. Defaults to `10` if omitted. Can also be set programmatically via `App::approx_tolerance(pct)`.

If the config file includes an `examples` field, Prolog<sup>2</sup> will immediately attempt to prove the examples as a query and output any learned hypotheses. 
If `examples` is omitted, an interactive REPL is started where queries can be entered manually.

The `auto` option makes the program iterate through all possible proofs in a query. By default this is off and after each proof the program awaits user input (Space/;: continue, Enter: stop).

`files`: a list of either directory or file paths. If a directory is found it recursively searches subdirectories and loads all files with a .pl extension

# Parallel Meta Interpretive Learning (PMIL)

## Top Program Construction (TPC)

Prolog<sup>2</sup> supports a parallel MIL learner, partially based on TPC as an alternative to the standard second order SLD-Resolution hypothesis search. TPC constructs the Top program — the set of clauses in all correct hypotheses — directly in polynomial time, then reduces it to remove redundant clauses using Plotkin's program reduction algorithm. This approach is based on the work of [Patsantzis and Muggleton (2021)](https://link.springer.com/article/10.1007/s10994-020-05945-w).

The TPC has three stages: **Generalise** generalise from each positive example in to collect all constructible clauses, **Specialise** removes any clause that entails a negative example, and **Reduce** applies Plotkin's reduction to eliminate redundant clauses while preferring general patterns over specific ones.

## PMIL pipeline

### Generalise

The **Parallel-MIL** pipline starts with a **Generalise** step. Running in parallel, each positve example starts a Prolog<sup>2</sup> query. Each query is exhaustively searched to find all proofs (and learnt hypotheses) for that example. These proofs are collected and sent to the next step as each thread produces them.

### Predicate Defintion Table

Each sub-hypothesis produced by generalisation threads may contain invented predicates, left as unbound vars. variable predicate clauses are extracted from incoming sub-hypotheses, grouped by the variable in the head, into an *ungrounded* **Predicate Defintion**. In the case of mutually recursive predicates these are grouped together into a single **Predicate Defintion** describing two (or more) predicates. These are then sorted by depdency, so that predicates appearing in the body literals of another defintion are unified against the table first.

Once **Predicate Defintions** are extracted and ordered they are inserted to the table. If a defintion can unifiy with another in the table no new defintion is inserted but variables shared by other incoming defintions are grounded through the unification. If the defintion can not unify with any in the table a new constant `pred_$n$` is coined for each head predicate in the defintion, and this *grounded* **Predicate Defintion** is added to the table.

A the end of this process all predicate symbols are grounded and the sub-hypothesis (now only containing the top level clauses) is described by a unified global set of invented predicate symbols, allowing for easy deduplication, a reduced memory usage for sub-hypotheses sharing **Predicate Definitions**.

### Coverage and Specialisation

Each sub-hypothesis collected by the above steps is then tested against the examples, in parallel. The negatives are queried first, against the sub-hypothesis and background knowledge, and the sub-hypothesis is dropped at the first one it entails. This is the **Specialisation** of TPC, done here per sub-hypothesis rather than per clause.

A sub-hypothesis entailing no negative then has each positive queried against it, to build a **Hypothesis Profile**: which positives it covers, along with its clause and literal counts, counting the **Predicate Definitions** it depends on.

If the surving profiled sub-hypotheses cover every positive between them, the examples are consistent and the pipeline moves straight on to **Sub Hypothesis Unification**.

### Noise Handling

This step only runs when some positive is left uncovered, meaning it is only entailed by sub-hypotheses that also entail negatives, or by none at all:

1. The dropped sub-hypotheses are profiled in full, this time recording every negative each one entails.
2. Each uncovered positive becomes a *conflict*: the positive, together with the minimal sets of negatives that would have to be ignored for some sub-hypothesis entailing it to be kept. A positive that no sub-hypothesis entails at all can only be left uncovered.
3. The cheapest *removal* is searched for: the fewest examples, positives left uncovered plus negatives ignored, that settles every conflict. Ignoring a set of negatives can settle several conflicts at once, so the choices are considered together rather than one positive at a time.
4. If a removal fits within `pos_noise` and `neg_noise`, those examples are filtered out and noted in the output, the sub-hypotheses that entail only ignored negatives are brought back, and every profile is restricted to the examples left.
5. If no removal fits, the run stops with a **Noise Report** on the examples of the cheapest removal found without the bounds. The report is described under [PMIL Usage](#pmil-usage).

### Sub Hypothesis Unification

A single sub-hypothesis only has to prove the example it was generalised from, so a complete hypothesis is usually the union of several. This step looks for the smallest groups of sub-hypotheses that cover every positive between them:

1. The profiles are sorted by positives covered (most first), then by clause count (fewest first), and optionally by literal count (`sort_by_literals`).
2. Any sub-hypothesis whose coverage is a subset of the coverage of one sorted ahead of it is discarded, as the other does at least as much for no greater cost.
3. A greedy cover is built, starting from the best profile and repeatedly adding the sub-hypothesis covering the most positives still uncovered. Its size `k` bounds the search that follows.
4. If `k` is 1, the sub-hypotheses covering every positive on their own are the result. Otherwise a backtracking search enumerates each combination of up to `k` sub-hypotheses that covers every positive, pruning any choice which covers too few of the remaining positives for the group to be completed within `k`.
5. Each complete group is checked against the negatives again. Two sub-hypotheses that each entail no negative can entail one together, since a clause from one can resolve with a clause from the other. A group that does is rejected and the search continues.
6. The search stops once `final_h_count` groups have been accepted.

Each accepted group is then turned into a program: the union of its clauses and the **Predicate Definitions** they depend on, with shared clauses and definitions included once. If `reduce` is set, Plotkin's reduction is applied to each program before it is printed.

## PMIL Usage

To enable PMIL, add a `"parallel"` block to your config file. Its presence is what selects PMIL over a direct query, so there is no separate on/off flag; an empty block `"parallel": {}` runs PMIL with every option at its default. The block takes five optional fields:<br>

`reduce`: run Plotkin's program reduction over each learned program. Off by default, which is useful for profiling or for inspecting the raw top program.<br>
`sort_by_literals`: when two candidate sub hypotheses tie on coverage and clause count, prefer the one with fewer body literals. Off by default. A tiebreaker only — it never outranks coverage or clause count.<br>
`final_h_count`: how many complete programs to return. Defaults to `5`. Many combinations of sub hypotheses usually cover every positive while proving no negative, and each costs a proof search against every negative to confirm, so this bounds how many are collected before the search stops.<br>
`neg_noise`: how many negative examples may be ignored as noise. Defaults to `0`.<br>
`pos_noise`: how many positive examples may be left uncovered as noise. Defaults to `0`.

The two noise options come into play when some positive example is only entailed by sub hypotheses that also entail negatives. That is one conflict with two ways out: leave the positive uncovered, or ignore those negatives. PMIL looks for the fewest examples whose removal leaves a consistent program, so a single positive that needs seven negatives ignored is the one set aside, and a single negative standing in the way of several positives is the one ignored.

If that removal fits within `pos_noise` and `neg_noise`, the examples are filtered out, the output notes which, and learning carries on with the rest. If it does not, the run stops and reports on the examples in the cheapest removal: which negatives a positive always comes with, example hypotheses that entail it, how they compare with hypotheses entailing no negative, and what a greedy program looks like with and without it. The report is printed and also written to `noise_report_<time stamp>.md` in the working directory. With both options at `0`, the default, any such conflict produces the report.

``` json
{
    "config" : {
        "max_depth": 5,
        "max_clause": 2
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
    "parallel" : {
        "reduce" : true
    },
    "files" : ["examples/trains/trains.pl"]
}
```

The same settings can be given in code. `App::config` and `App::parallel` each take a function from the settings so far to the ones to use, and each field has a method of its name:

``` rust
let app = App::default()
    .config(|config| config.max_depth(5).max_clause(2))
    .parallel(|parallel| parallel.reduce(true).pos_noise(1));
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
