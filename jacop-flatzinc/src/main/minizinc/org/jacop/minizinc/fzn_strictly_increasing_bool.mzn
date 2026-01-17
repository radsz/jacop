%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in strict increasing order
%-----------------------------------------------------------------------------%
predicate jacop_strictly_increasing(array[int] of var bool: x);

predicate fzn_strictly_increasing_bool(array[int] of var bool: x) =
   jacop_strictly_increasing(x);
