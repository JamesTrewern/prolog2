member(El, [El|_]).
member(El, [_|T]):-member(El,T).

map_list([],_).
map_list([H|T],P):-
    P(H),
    map_list(T,P).

map_list([],[],_).
map_list([H1|T1],[H2|T2],P):-
    P(H1,H2),
    map_list(T1,T2,P).