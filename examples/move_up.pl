succ(0).
succ(X):- Y is X - 1, succ(Y).

add(X,Y,Z):-
    Z is X + Y.

sub(X,Y,Z):-
    Z is X - Y.

P([A,B],[A,C]):-
    Q(D),
    R(B,D,C),
    {A,B,C,D}.


:- body_pred(succ,1), body_pred(add,3), body_pred(sub,3), max_h_clause(1).