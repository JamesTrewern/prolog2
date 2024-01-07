dad(adam, james).
dad(ken, adam).
dad(jim,ken).
mum(tami,james).
mum(lil,adam).

parent(X,Y):-dad(X,Y).
parent(X,Y):-mum(X,Y).

P(X,Y):-Q(X,Z),P(Z,Y)\X,Y,Z. 
P(X,Y):-Q(X,Y)\X,Y.


P(X,Y)<c>:-P(X,Y).
P(X,Y)<c>:-P(X,Z), P(Z,Y).