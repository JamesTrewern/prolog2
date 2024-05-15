dad(jim,ken).
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
P(X,Y):-Q(X,Z),P(Z,Y)\X,Y,Z. % Tail Recursion

:- body_pred(dad,2).
:- body_pred(mum,2).