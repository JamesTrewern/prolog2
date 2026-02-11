% ============================================
% BASE PREDICATES (Background Knowledge)
% ============================================
square_root(X,Y):- Y is -sqrt(X).
square_root(X,Y):- Y is sqrt(X).
neg(X,-X).
div(X,Y,Z):- Z is X / Y.
minus(X,Y,Z):- Z is X - Y.
add(X,Y,Z):- Z is X + Y.
mult(X,Y,Z):- Z is X * Y.
squared(X,Y):- Y is X * X.
times_two(X,Y):- Y is X * 2.

% ============================================
% META-RULES
% ============================================
% ORDERING PRINCIPLE: Rules are ordered so simpler Q predicates (smaller arity)
% are at the END of each section and get popped/tried FIRST due to LIFO.

% ============================================
% 4-PARAM: P(A,B,C,Res)
% ============================================
% Q:arity-4, R:arity-2 (tried LAST - most complex Q)
P(A,B,C,Res):- Q(A,B,C,Res1), R(Res1,Res), {P,Q,R}.

% Q:arity-4, R:arity-3 (one var reused)
P(A,B,C,Res):- Q(A,B,C,Res1), R(C,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,C,Res1), R(Res1,C,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,C,Res1), R(B,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,C,Res1), R(Res1,B,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,C,Res1), R(A,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,C,Res1), R(Res1,A,Res), {P,Q,R}.

% Q:arity-3, R:arity-3 (tried FIRST - simpler Q)
P(A,B,C,Res):- Q(B,C,Res1), R(A,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(B,C,Res1), R(Res1,A,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,C,Res1), R(B,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,C,Res1), R(Res1,B,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,Res1), R(C,Res1,Res), {P,Q,R}.
P(A,B,C,Res):- Q(A,B,Res1), R(Res1,C,Res), {P,Q,R}.

% ============================================
% 3-PARAM: P(A,B,Res)
% ============================================
% Q:arity-3, R:arity-3 (tried LAST - most complex Q)
P(A,B,Res):- Q(A,B,Res1), R(B,Res1,Res), {P,Q,R}.
P(A,B,Res):- Q(A,B,Res1), R(Res1,B,Res), {P,Q,R}.
P(A,B,Res):- Q(A,B,Res1), R(A,Res1,Res), {P,Q,R}.
P(A,B,Res):- Q(A,B,Res1), R(Res1,A,Res), {P,Q,R}.

% Q:arity-3, R:arity-2 (both A,B in Q)
P(A,B,Res):- Q(B,A,Res1), R(Res1,Res), {P,Q,R}.
P(A,B,Res):- Q(A,B,Res1), R(Res1,Res), {P,Q,R}.

% Q:arity-2, R:arity-3 (tried FIRST - simpler Q)
P(A,B,Res):- Q(B,Res1), R(A,Res1,Res), {P,Q,R}.
P(A,B,Res):- Q(B,Res1), R(Res1,A,Res), {P,Q,R}.
P(A,B,Res):- Q(A,Res1), R(B,Res1,Res), {P,Q,R}.
P(A,B,Res):- Q(A,Res1), R(Res1,B,Res), {P,Q,R}.

% ============================================
% 2-PARAM: P(A,Res)
% ============================================
% Q:arity-2, R:arity-3 (tried LAST)
P(A,Res):- Q(A,Res1), R(A,Res1,Res), {P,Q,R}.
P(A,Res):- Q(A,Res1), R(Res1,A,Res), {P,Q,R}.

% Q:arity-2, R:arity-2 (tried FIRST - simplest)
P(A,Res):- Q(A,Res1), R(Res1,Res), {P,Q,R}.
