
% Configuration options
:- body_pred(zero,1), body_pred(prev,2), max_h_clause(3), max_h_preds(1).

% Meta clauses
P(X):- Q(X) {X,Y}.
P(X):- Q(X,Y), R(Y) {X,Y}.





% Background Knowledge
zero(0).

prev(1,0).
prev(2,1).
prev(3,2).
prev(4,3).


% ?- even(4), not(even(3))





