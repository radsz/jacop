%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order
%-----------------------------------------------------------------------------%
predicate jacop_decreasing(array[int] of var int: x);

predicate fzn_decreasing_int(array[int] of var int: x) =
   jacop_decreasing(x);
