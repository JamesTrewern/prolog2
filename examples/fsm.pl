fsm(q0)?


fsm(Q1):-
    edge(Q1,Q2),
    fsm(Q2).

fsm(_):-
    goal.

goal:-
    observe(O),
    some_brackground_knowledge(O).

edge(Q1,Q2):-
    observe(Obs),
    P(Obs,Act),
    action(Act)
    {Obs, Act}.