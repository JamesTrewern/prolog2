% subset(?SubSet, +Set)
%
% Succeeds if SubSet is a subset of Set.
%
% Check mode  (SubSet bound): succeeds iff every element of SubSet is also
%   an element of Set.
% Generate mode (SubSet unbound): enumerates all subsets of Set, starting
%   with the largest and working down to the empty set, via backtracking.
%
% Implemented by trying each cardinality from |Set| down to 0 and delegating
% to the built-in subset/3 (which handles both check and generate at a fixed
% size).
subset(SubSet, Set) :-
    set_size(Set, Size),
    subset_by_size(SubSet, Set, Size).

% subset_by_size(?SubSet, +Set, +MaxSize)
%
% Helper for subset/2.  Tries all subset sizes from MaxSize down to 0,
% in that order, via backtracking.
subset_by_size(SubSet, Set, Size) :-
    subset(SubSet, Set, Size).
subset_by_size(SubSet, Set, Size) :-
    Size > 0,
    Size1 is Size - 1,
    subset_by_size(SubSet, Set, Size1).
