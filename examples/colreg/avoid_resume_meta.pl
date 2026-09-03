% --------------------------------------------------------
% ----------- Compliance Condition Clauses ---------------
% --------------------------------------------------------
P(X,Y,Z):- less_than(Z,A), Q(X,Y), {P,Q,A}.
P(X,Y,Z):- less_or_equal(Z,A), Q(X,Y), {P,Q,A}.
P(X,Y,Z):- greater_than(Z,A), Q(X,Y), {P,Q,A}.
P(X,Y,Z):- greater_or_equal(Z,A), Q(X,Y), {P,Q,A}.

P(X,Y,Z):- less_than(Z,A), less_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- less_than(Z,A), greater_than(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- less_than(Z,A), greater_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.

P(X,Y,Z):- greater_than(Z,A), less_than(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- greater_than(Z,A), less_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- greater_than(Z,A), greater_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.

P(X,Y,Z):- less_or_equal(Z,A), less_than(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- less_or_equal(Z,A), greater_than(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- less_or_equal(Z,A), greater_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.

P(X,Y,Z):- greater_or_equal(Z,A), less_than(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- greater_or_equal(Z,A), less_or_equal(Z,B), Q(X,Y), {P,Q,A,B}.
P(X,Y,Z):- greater_or_equal(Z,A), greater_than(Z,B), Q(X,Y), {P,Q,A,B}.