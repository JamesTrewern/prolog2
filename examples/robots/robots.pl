P(X,Y):- Q(M,X,Z), R(Z,Y), {P,Q,R}.
P(X,Y):- Q(X,Z), R(M,Z,Y), {P,Q,R}.
P(X,Y):- Q(M,X,Z), R(N,Z,Y), {P,Q,R}.
P(X,Y):- Q(X,Z), R(Z,Y), {P,Q,R}. 
P(X,Y):- Q(M,X,Y), {P,Q}.

higher_order_move(L):-
	higher_order_moves(Ms),
	functor(L,F,A),
	member(F/A,Ms).

double_move(M,Ss,Gs):-
	move(M),
	M(Ss,Ss_1),
	M(Ss_1,Gs).

triple_move(M,Ss,Gs):-
	move(M),
	M(Ss,Ss_1),
	double_move(M,Ss_1,Gs).

quadruple_move(M,Ss,Gs):-
	move(M),
	double_move(M,Ss,Ss_1),
	double_move(M,Ss_1,Gs).

move(move_right).
move(move_left).
move(move_up).
move(move_down).
% Compound actions - double moves
move(move_right_twice).
move(move_left_twice).
move(move_up_twice).
move(move_down_twice).
% Compound actions - angled moves
move(move_right_then_up).
move(move_right_then_down).
move(move_left_then_up).
move(move_left_then_down).
move(move_up_then_right).
move(move_up_then_left).
move(move_down_then_right).
move(move_down_then_left).

move_right_twice(Ss,Gs):-
	move_right(Ss,Ss_2),
	move_right(Ss_2,Gs).

move_left_twice(Ss,Gs):-
	move_left(Ss,Ss_2),
	move_left(Ss_2,Gs).

move_up_twice(Ss,Gs):-
	move_up(Ss,Ss_2),
	move_up(Ss_2,Gs).

move_down_twice(Ss,Gs):-
	move_down(Ss,Ss_2),
	move_down(Ss_2,Gs).

move_right_then_up(Ss,Gs):-
	move_right(Ss,Ss_2),
	move_up(Ss_2,Gs).

move_right_then_down(Ss,Gs):-
	move_right(Ss,Ss_2),
	move_down(Ss_2,Gs).

move_left_then_up(Ss,Gs):-
	move_left(Ss,Ss_2),
	move_up(Ss_2,Gs).

move_left_then_down(Ss,Gs):-
	move_left(Ss,Ss_2),
	move_down(Ss_2,Gs).

move_up_then_right(Ss,Gs):-
	move_up(Ss,Ss_2),
	move_right(Ss_2,Gs).

move_up_then_left(Ss,Gs):-
	move_up(Ss,Ss_2),
	move_left(Ss_2,Gs).

move_down_then_right(Ss,Gs):-
	move_down(Ss,Ss_2),
	move_right(Ss_2,Gs).

move_down_then_left(Ss,Gs):-
	move_down(Ss,Ss_2),
	move_left(Ss_2,Gs).

location(0,0).
location(0,1).
location(0,2).
location(0,3).
location(0,4).
location(1,0).
location(1,1).
location(1,2).
location(1,3).
location(1,4).
location(2,0).
location(2,1).
location(2,2).
location(2,3).
location(2,4).
location(3,0).
location(3,1).
location(3,2).
location(3,3).
location(3,4).
location(4,0).
location(4,1).
location(4,2).
location(4,3).
location(4,4).

move_down([0/1,G,4 - 4],[0/0,G,4 - 4]).
move_down([0/2,G,4 - 4],[0/1,G,4 - 4]).
move_down([0/3,G,4 - 4],[0/2,G,4 - 4]).
move_down([0/4,G,4 - 4],[0/3,G,4 - 4]).
move_down([1/1,G,4 - 4],[1/0,G,4 - 4]).
move_down([1/2,G,4 - 4],[1/1,G,4 - 4]).
move_down([1/3,G,4 - 4],[1/2,G,4 - 4]).
move_down([1/4,G,4 - 4],[1/3,G,4 - 4]).
move_down([2/1,G,4 - 4],[2/0,G,4 - 4]).
move_down([2/2,G,4 - 4],[2/1,G,4 - 4]).
move_down([2/3,G,4 - 4],[2/2,G,4 - 4]).
move_down([2/4,G,4 - 4],[2/3,G,4 - 4]).
move_down([3/1,G,4 - 4],[3/0,G,4 - 4]).
move_down([3/2,G,4 - 4],[3/1,G,4 - 4]).
move_down([3/3,G,4 - 4],[3/2,G,4 - 4]).
move_down([3/4,G,4 - 4],[3/3,G,4 - 4]).
move_down([4/1,G,4 - 4],[4/0,G,4 - 4]).
move_down([4/2,G,4 - 4],[4/1,G,4 - 4]).
move_down([4/3,G,4 - 4],[4/2,G,4 - 4]).
move_down([4/4,G,4 - 4],[4/3,G,4 - 4]).
move_left([1/0,G,4 - 4],[0/0,G,4 - 4]).
move_left([1/1,G,4 - 4],[0/1,G,4 - 4]).
move_left([1/2,G,4 - 4],[0/2,G,4 - 4]).
move_left([1/3,G,4 - 4],[0/3,G,4 - 4]).
move_left([1/4,G,4 - 4],[0/4,G,4 - 4]).
move_left([2/0,G,4 - 4],[1/0,G,4 - 4]).
move_left([2/1,G,4 - 4],[1/1,G,4 - 4]).
move_left([2/2,G,4 - 4],[1/2,G,4 - 4]).
move_left([2/3,G,4 - 4],[1/3,G,4 - 4]).
move_left([2/4,G,4 - 4],[1/4,G,4 - 4]).
move_left([3/0,G,4 - 4],[2/0,G,4 - 4]).
move_left([3/1,G,4 - 4],[2/1,G,4 - 4]).
move_left([3/2,G,4 - 4],[2/2,G,4 - 4]).
move_left([3/3,G,4 - 4],[2/3,G,4 - 4]).
move_left([3/4,G,4 - 4],[2/4,G,4 - 4]).
move_left([4/0,G,4 - 4],[3/0,G,4 - 4]).
move_left([4/1,G,4 - 4],[3/1,G,4 - 4]).
move_left([4/2,G,4 - 4],[3/2,G,4 - 4]).
move_left([4/3,G,4 - 4],[3/3,G,4 - 4]).
move_left([4/4,G,4 - 4],[3/4,G,4 - 4]).
move_right([0/0,G,4 - 4],[1/0,G,4 - 4]).
move_right([0/1,G,4 - 4],[1/1,G,4 - 4]).
move_right([0/2,G,4 - 4],[1/2,G,4 - 4]).
move_right([0/3,G,4 - 4],[1/3,G,4 - 4]).
move_right([0/4,G,4 - 4],[1/4,G,4 - 4]).
move_right([1/0,G,4 - 4],[2/0,G,4 - 4]).
move_right([1/1,G,4 - 4],[2/1,G,4 - 4]).
move_right([1/2,G,4 - 4],[2/2,G,4 - 4]).
move_right([1/3,G,4 - 4],[2/3,G,4 - 4]).
move_right([1/4,G,4 - 4],[2/4,G,4 - 4]).
move_right([2/0,G,4 - 4],[3/0,G,4 - 4]).
move_right([2/1,G,4 - 4],[3/1,G,4 - 4]).
move_right([2/2,G,4 - 4],[3/2,G,4 - 4]).
move_right([2/3,G,4 - 4],[3/3,G,4 - 4]).
move_right([2/4,G,4 - 4],[3/4,G,4 - 4]).
move_right([3/0,G,4 - 4],[4/0,G,4 - 4]).
move_right([3/1,G,4 - 4],[4/1,G,4 - 4]).
move_right([3/2,G,4 - 4],[4/2,G,4 - 4]).
move_right([3/3,G,4 - 4],[4/3,G,4 - 4]).
move_right([3/4,G,4 - 4],[4/4,G,4 - 4]).
move_up([0/0,G,4 - 4],[0/1,G,4 - 4]).
move_up([0/1,G,4 - 4],[0/2,G,4 - 4]).
move_up([0/2,G,4 - 4],[0/3,G,4 - 4]).
move_up([0/3,G,4 - 4],[0/4,G,4 - 4]).
move_up([1/0,G,4 - 4],[1/1,G,4 - 4]).
move_up([1/1,G,4 - 4],[1/2,G,4 - 4]).
move_up([1/2,G,4 - 4],[1/3,G,4 - 4]).
move_up([1/3,G,4 - 4],[1/4,G,4 - 4]).
move_up([2/0,G,4 - 4],[2/1,G,4 - 4]).
move_up([2/1,G,4 - 4],[2/2,G,4 - 4]).
move_up([2/2,G,4 - 4],[2/3,G,4 - 4]).
move_up([2/3,G,4 - 4],[2/4,G,4 - 4]).
move_up([3/0,G,4 - 4],[3/1,G,4 - 4]).
move_up([3/1,G,4 - 4],[3/2,G,4 - 4]).
move_up([3/2,G,4 - 4],[3/3,G,4 - 4]).
move_up([3/3,G,4 - 4],[3/4,G,4 - 4]).
move_up([4/0,G,4 - 4],[4/1,G,4 - 4]).
move_up([4/1,G,4 - 4],[4/2,G,4 - 4]).
move_up([4/2,G,4 - 4],[4/3,G,4 - 4]).
move_up([4/3,G,4 - 4],[4/4,G,4 - 4]).