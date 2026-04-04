'='(X,X).

% atomic/1 - succeeds for constants, strings, and numbers.
atomic(X) :- is_const(X).
atomic(X) :- is_number(X).
atomic(X) :- is_string(X).

true.