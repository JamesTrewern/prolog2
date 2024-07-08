:- ['examples/robots/examples'].

P(X,Y):- Q(M,X,Z), R(Z,Y) {X,Y,Z}.
P(X,Y):- Q(X,Z), R(M,Z,Y) {X,Y,Z}.
P(X,Y):- Q(M,X,Z), R(N,Z,Y) {X,Y,Z}.

:- max_h_clause(4), max_h_preds(2), debug(false).

:- load_module(top_prog).

background_knowledge([
	move_right/2,
	move_left/2,
	move_up/2,
	move_down/2,
	double_move/3,
	triple_move/3,
	quadruple_move/3,
	move_right_twice/2,
	move_left_twice/2,
	move_up_twice/2,
	move_down_twice/2,
	move_right_then_up/2,
	move_right_then_down/2,
	move_left_then_up/2,
	move_left_then_down/2,
	move_up_then_right/2,
	move_up_then_left/2,
	move_down_then_right/2,
	move_down_then_left/2
]).


test:-
	pos_examples(Pos),
	learn(Pos,[],H).

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
