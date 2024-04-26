dad(ken,adam).
dad(adam,james).
mum(tami,james). 

P(X,Y):-Q(X,Y)\X,Y.
P(A,B):<c>-P(A,B).

P(X,Y):-Q(X,Z),P(Z,Y)\X,Y,Z. % Tail Recursion
P(A,B):<c>-P(A,C),P(C,B).


% ancestor(X,Y):-dad(X,Z),ancestor(Z,Y).
% ancestor(X,Y):-dad(X,Y).

