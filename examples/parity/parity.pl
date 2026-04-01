fsm(Input,Result):-
    q0(Q0),
    fsm(Input,Q0,Result).

fsm([],State,State).
fsm([H|T],Q1,State):-
    edge(H,Q1,Q2),
    fsm(T,Q2,State).

edge(El,Q1,Q2):-
    q(Q1),
    q(Q2),
    {El},[Q1,Q2].

q0(even).
q(even).
q(odd).