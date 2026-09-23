% Turn
P(X,Z):- less_than(Z,A), Q(X), {P,Q,A}.
P(X,Z):- less_or_equal(Z,A), Q(X), {P,Q,A}.
P(X,Z):- greater_than(Z,A), Q(X), {P,Q,A}.
P(X,Z):- greater_or_equal(Z,A), Q(X), {P,Q,A}.

P(X,Z):- less_than(Z,A), less_or_equal(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- less_than(Z,A), greater_than(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- less_than(Z,A), greater_or_equal(Z,B), Q(X), {P,Q,A,B}.

P(X,Z):- greater_than(Z,A), less_than(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- greater_than(Z,A), less_or_equal(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- greater_than(Z,A), greater_or_equal(Z,B), Q(X), {P,Q,A,B}.

P(X,Z):- less_or_equal(Z,A), less_than(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- less_or_equal(Z,A), greater_than(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- less_or_equal(Z,A), greater_or_equal(Z,B), Q(X), {P,Q,A,B}.

P(X,Z):- greater_or_equal(Z,A), less_than(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- greater_or_equal(Z,A), less_or_equal(Z,B), Q(X), {P,Q,A,B}.
P(X,Z):- greater_or_equal(Z,A), greater_than(Z,B), Q(X), {P,Q,A,B}.
