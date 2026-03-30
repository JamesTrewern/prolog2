'='(X,X).
is_number(X):-is_float(X).
is_number(X):-is_int(X).
is_list([]).
is_list([_|T]):-
    is_list(T).