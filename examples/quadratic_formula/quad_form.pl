square_root(X,Y):- Y is -sqrt(X).
square_root(X,Y):- Y is sqrt(X).
neg(X,-X).
div(X,Y,Z):- Z is X / Y.
minus(X,Y,Z):- Z is X - Y.
add(X,Y,Z):- Z is X + Y.
mult(X,Y,Z):- Z is X * Y.
squared(X,Y):- Y is X * X.
const(1). 
const(2). 
const(3). 
const(4). 
const(5).

quad(A,B,C,X):-numerator(A,B,C,Res1),quad_2(A,Res1,X).
quad_2(A,Numerator,Res):-
    times_2(A,Res1),
    div(Numerator,Res1,Res).

times_2(A,Res):-
    const(2),
    mult(A,2,Res).
times_four(X,Res):-
    const(4),
    mult(X,4,Res).

four_a_c(A,C,Res):-
    mult(A,C,Res1),
    times_four(Res1,Res).

discriminant(A,B,C,Res):-
    four_a_c(A,C,Res1),
    discriminant_1(Res1,B,Res).

discriminant_1(AC4,B,Res):-
    squared(B,Res1),
    minus(Res1,AC4,Res).

numerator(A,B,C,Res):-
    numerator_right(A,B,C,Res1),
    numerator_1(B,Res1,Res).

numerator_1(B,NumRight,Res):-
    neg(B,Res1),
    add(Res1,NumRight,Res).

numerator_right(A,B,C,Res):-
    discriminant(A,B,C,Res1),
    square_root(Res1,Res).
