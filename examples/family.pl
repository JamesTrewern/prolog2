dad(jim,ken)
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
dad(ken,kelly).
dad(chris,tami).
dad(adam,luke).
mum(tami,james).
mum(tami,luke).
mum(lil,adam).
mum(lil,kelly).
mum(lil,saul).
mum(christine,tami).

P(X,Y):-Q(X,Y)\X,Y.
P(A,B):<c>-P(A,B).

P(X,Y):-Q(X,Z),P(Z,Y)\X,Y,Z. % Tail Recursion
P(A,B):<c>-P(A,C),P(C,B).