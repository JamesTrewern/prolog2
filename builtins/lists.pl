member(El, [El]).
member(El, [El|T]).
member(El, [H|T]):-member(El,T).

forall([],P).
forall([H|T],P):-
    P(H),
    forall(T,P).
forall([H|T],P(A)):-
    P(H,A),
    forall(T,P(A)).
forall([H|T],P(A,B)):-
    P(H,A,B),
    forall(T,P(A,B)).
forall([H|T],P(A,B,C)):-
    P(H,A,B,C),
    forall(T,P(A,B,C)).