mum(tami,james).
mum(tami,luke).
mum(lil,adam).
mum(lil,kelly).
mum(lil,saul).
mum(christine,tami).
dad(jim,ken).
dad(ken,adam).
dad(adam,james).
dad(ken,saul).
dad(ken,kelly).
dad(chris,tami).
dad(adam,luke).

P(X,Y):-Q(X,Y), {X,Y}.
P(X,Y):-Q(X,Z),P(Z,Y), {X,Y,Z}. % Tail Recursion


% :-body_pred(mum,2), body_pred(dad,2), max_h_clause(4), max_h_preds(1), max_depth(10).