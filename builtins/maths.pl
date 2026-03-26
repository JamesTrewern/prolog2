% succ(X, Y) - Y is the successor of X (Y = X + 1).
% Works with either argument unbound.
succ(X, Y) :- Y is X + 1.
succ(X, Y) :- X is Y - 1.

% plus(X, Y, Z) - Z = X + Y.
% Works with any one argument unbound.
plus(X, Y, Z) :- Z is X + Y.
plus(X, Y, Z) :- X is Z - Y.
plus(X, Y, Z) :- Y is Z - X.

% minus(X, Y, Z) - Z = X - Y.
% Works with any one argument unbound.
minus(X, Y, Z) :- Z is X - Y.
minus(X, Y, Z) :- X is Z + Y.
minus(X, Y, Z) :- Y is X - Z.

% times(X, Y, Z) - Z = X * Y.
% Works with any one argument unbound.
times(X, Y, Z) :- Z is X * Y.
times(X, Y, Z) :- X is Z / Y.
times(X, Y, Z) :- Y is Z / X.

% divide(X, Y, Z) - Z = X / Y.
% Works with any one argument unbound.
divide(X, Y, Z) :- Z is X / Y.
divide(X, Y, Z) :- X is Z * Y.
divide(X, Y, Z) :- Y is X / Z.

% pow(X, Y, Z) - Z = X raised to the power Y.
pow(X, Y, Z) :- Z is X ** Y.

% mod(X, Y, Z) - Z = X mod Y (truncating towards zero).
mod(X, Y, Z) :- Z is X - (X / Y) * Y.

% abs(X, Y) - Y = absolute value of X.
abs(X, Y) :- Y is abs(X).

% negate(X, Y) - Y = -X.
% Works with either argument unbound.
negate(X, Y) :- Y is -X.
negate(X, Y) :- X is -Y.

% sqrt(X, Y) - Y = square root of X.
% Works with either argument unbound: sqrt(X, Y) finds Y, sqrt(X, Y) with Y bound finds X = Y^2.
sqrt(X, Y) :- Y is sqrt(X).
sqrt(X, Y) :- X is Y * Y.

% round(X, Y) - Y = X rounded to the nearest integer.
round(X, Y) :- Y is round(X).

% max(X, Y, Z) - Z = the larger of X and Y.
max(X, Y, X) :- X >= Y.
max(X, Y, Y) :- Y > X.

% min(X, Y, Z) - Z = the smaller of X and Y.
min(X, Y, X) :- X =< Y.
min(X, Y, Y) :- Y < X.

% between(Low, High, X) - succeeds if X satisfies Low =< X =< High.
% Check mode only: all three arguments must be bound. Works for integers and floats.
between(Low, High, X) :- Low =< X, X =< High.
