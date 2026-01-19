zero(0).
prev(1,0).
prev(2,1).
prev(3,2).
prev(4,3).

P(X):- Q(X,Y), R(Y) {P,Q,R}.
P(X):- Q(X) {P,Q}.


% ?- even(4), not(even(3))





