:- ['examples/coloured_graph/ambiguities'].
:- ['examples/coloured_graph/false_negatives'].
:- ['examples/coloured_graph/false_positives'].
:- ['examples/coloured_graph/no_noise'].

ancestor(A,B):-parent(A,B).
ancestor(C,D):-parent(C,E),ancestor(E,D).

parent(A,B):-blue_parent(A,B).
parent(C,D):-red_parent(C,D).

blue_parent(a,c).
blue_parent(a,n).
blue_parent(b,i).
blue_parent(b,d).
blue_parent(c,j).
blue_parent(d,e).
blue_parent(f,g).
blue_parent(f,h).

red_parent(k,c).
red_parent(k,n).
red_parent(l,i).
red_parent(l,d).
red_parent(i,j).
red_parent(m,e).
red_parent(n,g).
red_parent(n,h).

P(X,Y):-Q(X,Y) {X,Y}.
P(X,Y):-Q(Y,X) {X,Y}.

P(X,Y):- Q(X,Z), R(Y,Z) {X,Y,Z}.
P(X,Y):- Q(Z,X), R(Z,Y) {X,Y,Z}.

:- background_knowledge([ancestor/2]).

:- max_h_clause(3), max_h_preds(0), debug(false).

:- load_module(top_prog).