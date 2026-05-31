member(El, [El|_]).
member(El, [_|T]):-member(El,T).

%Branch Based on Condition form
list_for_all(List,Cond):-
    valid_functor(Cond),
    list_for_all_1(List,Cond).
list_for_all(List,Cond):-
    Cond =.. CondList,
    list_for_all_2(List,CondList).
%Simple list for all
list_for_all_1([],_).
list_for_all_1([H|T],P):-
    P(H),
    list_for_all_1(T,P).
%List for all with curried argument
list_for_all_2([],_).
list_for_all_2([H|T],[P,A]):-
    P(A,H),
    list_for_all_2(T,[P,A]).
list_for_all_2([H|T],[P,A,B]):-
    P(A,B,H),
    list_for_all_2(T,[P,A,B]).


map_list([],[],_).
map_list([H1|T1],[H2|T2],P):-
    P(H1,H2),
    map_list(T1,T2,P).

%% Count True 
% ---------------------------
%initial call
count_true([H|T],P,N):-
    valid_functor(P),
    count_true_1([H|T],P,0,N).
count_true([H|T],Cond,N):-
    Cond=..CondList,
    count_true_2([H|T],CondList,0,N).
%base case    
count_true_1([],P,N,N).
count_true_2([],P,N,N).

count_true_1([H|T],P,N1,N2):-
    P(H),
    N3 is N1 + 1,
    count_true_1(T,P,N3,N2).
count_true_1([H|T],P,N1,N2):-
    not(P(H)),
    count_true_1(T,P,N1,N2).

count_true_2([H|T],[P,A],N1,N2):-
    P(A,H),
    N3 is N1 + 1,
    count_true_2(T,[P,A],N3,N2).
count_true_2([H|T],[P,A],N1,N2):-
    not(P(A,H)),
    count_true_2(T,[P,A],N1,N2).