%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in strict decreasing order
%-----------------------------------------------------------------------------%
predicate jacop_strictly_decreasing(array[int] of var bool: x);

predicate fzn_strictly_decreasing_bool(array[int] of var bool: x) =
   jacop_strictly_decreasing(x);
