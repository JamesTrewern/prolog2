fsm(q0)?

fsm(Q1):-
    edge(Q1,Q2),
    fsm(Q2).

fsm(_):-
    goal.

goal:-
    observe(O),
    some_brackground_knowledge(O).

edge(Q1,Q2, State):-
    observe(Obs, State),
    P(State,Act),
    action(Act, State)
    {Q1, Q2, P}.