fsm([],State,State).

fsm([H|T],Q1,State):-
    edge(H,Q1,Q2),
    fsm(T,Q2,State).

edge(El,Q1,Q2):-
    q(Q1),
    q(Q2),
    {El,Q1,Q2}.

q(even).
q(odd).