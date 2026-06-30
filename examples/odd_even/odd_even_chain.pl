zero(0,0).
prev(1,0).
prev(2,1).
prev(3,2).
prev(4,3).
prev(5,4).

P(X,Y):-Q(X,Z),R(Z,Y). 

% Query
% ----------------------------
% even(4,X), not(even(3,X)).
% ----------------------------
% Expected Theory
% ----------------------------
% even(X,Y):-prev(X,Z),p1(Z,Y).
% p1(X,Y):-prev(X,Z),even(Z,Y).
% p1(X,Y):-prev(X,Z),zero(Z,Y)
% ----------------------------