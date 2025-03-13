hanoi_start(N,s(Stack2,[],[])):-
    stack(N,Stack1),
    reverse(Stack1,Stack2).

stack(0,[]).
stack(N,[N|Stack]):-
    N >= 0,
    N1 is N - 1,
    stack(N1,Stack).

move_1_2(s(S1,S2,S3),s(S4,S5,S3)):-
    move(S1,S2,S4,S5).

move_1_3(s(S1,S2,S3),s(S4,S2,S6)):-
    move(S1,S3,S4,S6).

move_2_1(s(S1,S2,S3),s(S4,S5,S3)):-
    move(S2,S1,S5,S4).

move_2_3(s(S1,S2,S3),s(S1,S5,S6)):-
    move(S2,S3,S5,S6).

move_3_1(s(S1,S2,S3),s(S4,S2,S6)):-
    move(S3,S1,S6,S4).

move_3_2(s(S1,S2,S3),s(S1,S5,S6)):-
    move(S3,S2,S6,S5).

move([Top1|Stack1],[Top2|Stack2],Stack1,[Top1,Top2|Stack2]):-
    Top1 < Top2.
move([Top1|Stack1],[],Stack1,[Top1]).

% test:-
%     hanoi_start(3,S),
%     move_1_3(S,S1),
%     move_1_2(S1,S2),
%     move_3_2(S2,S3),
%     move_1_3(S3,S4),
%     move_2_1(S4,S5),
%     move_2_3(S5,S6),
%     move_1_3(S6,S7),
%     write(S7).

%MIL ------------------------------

goal_state(s([],[],[1,2,3])).

q(q0).
q(q1).
q(q2).
q(q3).

fsm(_,State):-
    goal_state(State).
fsm(Q1,State1):-
    edge(Q1,State1, Q2, State2),
    fsm(Q2, State2).

edge(Q1,State1,Q2,State2):-
    q(Q2),
    Q1 =/= Q2,
    P(State1,State2),
    {Q1, Q2, P}.

:- body_pred(move_1_2),body_pred(move_1_3),body_pred(move_2_1),body_pred(move_2_3),body_pred(move_3_1),body_pred(move_3_2),
:- max_h_clause(7), max_h_preds(0), max_depth(100), debug(true).

test:-
    hanoi_start(3,S),
    fsm(q0,S).

% edge(Q1,State1,Q2,State2):-
%     q(Q2)
%     P(State1),
%     Q(State1,State2),
%     {Q1, Q2, P, Q}.