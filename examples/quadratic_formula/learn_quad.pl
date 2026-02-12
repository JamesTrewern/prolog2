% ============================================
% BASE PREDICATES (Background Knowledge)
% ============================================
square_root(X,Y):- Y is -sqrt(X).
square_root(X,Y):- Y is sqrt(X).
neg(X,-X).
div(X,Y,Z):- Z is X / Y.
minus(X,Y,Z):- Z is X - Y.
add(X,Y,Z):- Z is X + Y.
mult(X,Y,Z):- Z is X * Y.
squared(X,Y):- Y is X * X.


