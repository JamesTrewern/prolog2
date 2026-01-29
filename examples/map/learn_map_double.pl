Map([],[], X), {Map}.

Map([H1|T1], [H2|T2], P):-
    P(H1,H2),
    Map(T1, T2, P),
    {Map, P}.

P(X,Y):-Q(X,X,Y),{P,Q}.

add(X,Y,Z):- Z is X + Y.