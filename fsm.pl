fsm(Q1,WM1,[Output|Stream]):-
    edge(Q1,WM1,WM2,Output,Q2),
    fsm(Q2,WM2,Stream).

fsm(S,_,[]).

edge(Q1,WM1,WM2,Output,Q2):-P(WM1,WM2)\WM1,WM2.