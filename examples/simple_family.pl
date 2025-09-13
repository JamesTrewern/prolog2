mum(tami,james).
mum(christine,tami).
dad(ken,adam).
dad(adam,james).

P(X,Y):-Q(X,Y), {X,Y}.

:-body_pred(mum,2).
:-body_pred(dad,2).