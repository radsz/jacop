%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order
%-----------------------------------------------------------------------------%
predicate jacop_increasing(array[int] of var bool: x);

predicate fzn_increasing_bool(array[int] of var bool: x) =
   jacop_increasing(x);
