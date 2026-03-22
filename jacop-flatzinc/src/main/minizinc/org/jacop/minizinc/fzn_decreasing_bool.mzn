%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in decreasing order
%-----------------------------------------------------------------------------%
predicate jacop_decreasing(array[int] of var bool: x);

predicate fzn_decreasing_bool(array[int] of var bool: x) =
   jacop_decreasing(x);
