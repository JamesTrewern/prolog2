map([],[], X).

map([H1|T1], [H2|T2], P):-
    P(H1,H2),
    map(T1, T2, P).

double(X,Y):-
    Y is X + X.
