# Prolog<sup>2</sup>

Prolog<sup>2</sup> is a machine learning and logic programming framework, that implements native second-order logic and SLD resolution. This is an extension of Meta-Interpretive Learning, which was first used in 
[Meta-interpretive learning of higher-order dyadic datalog: predicate invention revisited](https://link.springer.com/article/10.1007/s10994-014-5471-y?fromPaywallRec=false)

This project aims to allow for more complex formations of second-order clauses and resolution.

# Defining second order clauses

Traditional meta-rules can be written simply by making predicate symbols start with upper case letters. 
We must define which variables will remain as variables when a new clause is created from this higher-order clause.
We define these universally quantified variables using curly braces like so:  `{X,Y}` 

```prolog
P(X,Y):- Q(X,Y) {X,Y}. %Identity

P(X,Y):- Q(X,Z), R(Z,Y) {X,Y}. %Chain

P(X,Y):- Q(X,Z), P(Z,Y) {X,Y}. %Tail Recursion
```


With this more flexible notation many we can create many more interesting second-order clauses </br> 
for example, we can introduce certain constant predicate symbols either in the head or body to allow us to have greater control over the clauses that will be learnt.
We can also create second-order clauses with only constant predicate symbols but existentially and universally quantified variables to denote the introduction of some constants

``` prolog
p(X,Y):- Q(X), R(Y) {X,Y}.

P(X,Y):- q(X,Y), R(Y) {X,Y}.

p(X,Y):- q(X,Z), R(Z,Y) {X,Y}. %matching with this clause will create a new clause where Z is a constant
```

This can even be extended to using infix operators in second-order clauses

``` prolog
P(X,Y):- X > Y, Q(Y) {X,Y}.

P(X,Y):- Z is X + Y, Q(Z) {X,Y,Z}.
```

# Example usage

## Family relations

first, we lay out our background knowledge.</br> 
What would have been called meta-rules is now better described as second-order clauses, where {X,Y} denotes that the X and Y variables are universally quantified. 

The usage of the directive body_pred here tells the program that goals with variable symbols can match clauses of that symbol and arity.


``` prolog

mum(tami,james).
mum(tami,luke).
mum(christine,tami).
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
dad(ken,kelly).
dad(adam,luke).

P(X,Y):-Q(X,Y) {X,Y}.
P(X,Y):-Q(X,Z),P(Z,Y) {X,Y,Z}. % Tail Recursion

:-body_pred(mum,2).
:-body_pred(dad,2).

```

With this file loaded we can then pose a query and a hypothesis will be returned

``` prolog
?-ancestor(ken,james).

TRUE
ancestor(ken,james),
Hypothesis:
        ancestor(A,B):-dad(A,C),ancestor(C,B)
        ancestor(A,B):-dad(A,B)
```

# Configuration Options
``` prolog

:-body_pred(mum,2).
:-max_h_preds(0).                %How many predicate symbols can be invented in the hypothesis
:-max_h_clause(0).               %How many clauses can the learner create.
:-debug(true).                   %Output Debugging statements whilst solving
:-load_module(maths).            %Import built-in module (So far only maths)
:- load_file('examples/family'). %Load file at path
:- ['examples/family'].
```
