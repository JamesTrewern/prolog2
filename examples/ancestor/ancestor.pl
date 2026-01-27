% Family facts
mum(tami,james).
mum(tami,luke).
mum(christine,tami).
dad(ken,adam).
dad(adam,james).

% Meta-rules for learning ancestor
P(X,Y):-Q(X,Y), {P,Q}.
P(X,Y):-Q(X,Z),P(Z,Y), {P,Q}.
