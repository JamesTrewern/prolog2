map([],[]).

map([H1|T1], [H2|T2], P):-
    P(H1,H2).