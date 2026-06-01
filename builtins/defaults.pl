'='(X,X).

% atomic/1 - succeeds for constants, strings, and numbers.
atomic(X) :- const(X).
atomic(X) :- number(X).
atomic(X) :- string(X).

true.