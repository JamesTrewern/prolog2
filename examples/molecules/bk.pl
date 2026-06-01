% ------------------------------------------------------------------
% Molecule Traversal
% ------------------------------------------------------------------
subs(X, Subs):-
	nonvar(X),
	X = (_,_,Subs).
ring_members(X, Members):-
	nonvar(X),
	X = ring(_,Members).

children(X,Y):-subs(X,Y).
children(X,Y):-ring_members(X,Y).

sub_structure(X, X).
sub_structure(X, Y):- 
	children(X, Cs),
	member(C, Cs),
	sub_structure(C, Y).
% ------------------------------------------------------------------
% Feature Extractors 
% ------------------------------------------------------------------
element(E,X):-
	nonvar(X),
	X = (_,E,_).
element(h,h).
bond_type(B,X):-
	nonvar(X),
	X = (B,_,_).
bond_type(B,X):-
	nonvar(X),
	X = ring(B,_).


branching(N,(B,S,Subs)):-
	length(Subs, N).
ring_size(N,ring(B,Members)):-
	length(Members,N).
	
bound_element_count(El,N,X):-
	subs(X,Subs),
	count_true(Subs,element(El),N).
ring_element_count(El,N,X):-
	ring_members(X,Members),
	count_true(Members,element(El),N).

% ------------------------------------------------------------------
% Adjacency 
% ------------------------------------------------------------------
bound(X,Y):-
	nonvar(X),
	subs(X,Subs),
	member(Y,Subs).
ring_member(X,Y):-
	nonvar(X),
	ring_members(X,Members),
	member(Y,Members).
limb(R, L):- 
	nonvar(R),
	ring_member(R, M),
	bound(M, L).

% ------------------------------------------------------------------
% Meta Rules 
% ------------------------------------------------------------------
P(X,X) :- Q(A,X),            {P,Q}, [A].        % 2-arity feature
P(X,X) :- Q(A,B,X),          {P,Q}, [A,B].      % 3-arity feature
P(X,X) :- Q(A,X), R(B,C,X),  {P,Q,R}, [A,B,C].  % 2-arity ∧ 3-arity

% Chain: navigate through two steps
P(X, Y) :- Q(X, Y), R(Y, Z), {P, Q, R}.

% Branch: take two different traversal steps from the same node
P(X,X) :- Q(X,Y), R(X,Z), {P,Q,R}.

% ------------------------------------------------------------------
% Learning Wrapper 
% ------------------------------------------------------------------
hydroxyl(MolName):-
    MolName(MolTerm),
    sub_structure(MolTerm,SubStruct),
    hydroxyl(SubStruct,Y).

phenolic(MolName):-
    MolName(MolTerm),
    sub_structure(MolTerm,SubStruct),
    phenolic(SubStruct,Y).