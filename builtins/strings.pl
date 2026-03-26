% string_to_atom/2 - alias for atom_string/2 with reversed argument order.
string_to_atom(String, Atom) :- atom_string(Atom, String).

% atomic/1 - succeeds for atoms, strings, and numbers.
atomic(X) :- number(X).
atomic(X) :- atom(X).
atomic(X) :- string(X).

% atomic_list_concat/2 - concatenate a list of atoms (and strings/numbers) into one atom.
% The result is always an atom.  Each element is converted to text first.
atomic_list_concat([X], R) :- term_string(X, S), atom_string(R, S).
atomic_list_concat([H|T], R) :- atomic_list_concat(T, Rest), term_string(H, S), atom_string(H2, S), atom_concat(H2, Rest, R).
