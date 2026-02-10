% Test sqrt function
test_sqrt(X) :- X is sqrt(16).
test_sqrt2(X) :- X is sqrt(2).

% Test unary negation
test_neg(X) :- X is -(5).
test_neg2(X) :- X is -(3.14).

% Test unary negation in expression
test_neg_expr(X) :- X is 10 + -(5).

% Test binary subtraction still works
test_sub(X) :- X is 10 - 3.

% Combined test
test_combined(X) :- X is sqrt(-(-(25))).

% Test negative sqrt
square_root(X,Y):- Y is -sqrt(X).

% Test negative variable in fact head
neg(X,-X).
