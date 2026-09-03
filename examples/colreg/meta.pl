% --------------------------------------------------------
% ---------------- Take action clauses  ------------------
% --------------------------------------------------------
P(X):- Q(X), R(X), {P,Q,R}. % Branch with agent
P(X):- Q(X,Y), R(X,Y), {P,Q,R}. % Branch with shared vessel
P(X):- Q(X,Y), {P,Q}.
P(X):- Q(X,Z,A), {P,Q,A}. % Property true for any vessel
P(X):- Q(X,Z,A,B), {P,Q,A,B}. % Property true for any vessel


% --------------------------------------------------------
% ---------------- Vessel Pair Clauses  ------------------
% --------------------------------------------------------

P(X,Y):- Q(X,Y), R(X,Y), {P,Q,R}. % Branch
P(X,Y):- Q(X,Y,A), [P,Q,A]. % Has 1 constant property
P(X,Y):- Q(X,Y,A,B), [P,Q,A,B]. % Has 2 constant property

% --------------------------------------------------------
% ----------------- Transitive Values --------------------
% --------------------------------------------------------

% % Single Comparison
% P(X,Y):-
%     tcpa(X,Y,Z),
%     comparitor(Q),
%     Q(Z,A),
%     [P,Q,A].
% P(X,Y):-
%     dcpa(X,Y,Z),
%     comparitor(Q),
%     Q(Z,A),
%     [P,Q,A].
% P(X,Y):-
%     range(X,Y,Z),
%     comparitor(Q),
%     Q(Z,A),
%     [P,Q,A].
% % Double comparison
% P(X,Y):-
%     tcpa(X,Y,Z),
%     comparitor(Q),
%     comparitor(R),
%     Q(Z,A),
%     R(Z,B),
%     {Q,R},
%     [P,A,B].
% P(X,Y):-
%     dcpa(X,Y,Z),
%     comparitor(Q),
%     comparitor(R),
%     Q(Z,A),
%     R(Z,B),
%     {Q,R},
%     [P,A,B].
% P(X,Y):-
%     range(X,Y,Z),
%     comparitor(Q),
%     comparitor(R),
%     Q(Z,A),
%     R(Z,B),
%     {Q,R},
%     [P,A,B].