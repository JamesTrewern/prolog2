mum(tami,james).
% mum(tami,luke).
mum(christine,tami).
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
% dad(ken,kelly).
% dad(adam,luke).

P(X,Y):-Q(X,Y), {P,Q}.
P(X,Y):-Q(X,Z),P(Z,Y), {P,Q}.


