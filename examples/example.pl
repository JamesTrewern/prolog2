map(_,P).
map(P,[H|T]):-P(H),map(P,T).

P(X,Y):-Q(X,Y), {P,Q}. % Identity
P(X,Y):-Q(X,Z),P(Z,Y), {P,Q}. % Tail Recursion

fsm([]).
fsm(Q1, [Input|T]):-
    edge(Q1,Input, Q2),
    fsm(Q2, T).

edge(Q1,Input,Q2):-
    P(Input),
    {Q1,Q2,P}.



    