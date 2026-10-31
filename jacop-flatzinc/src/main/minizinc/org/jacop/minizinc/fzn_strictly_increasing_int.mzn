%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in strict increasing order
%-----------------------------------------------------------------------------%
predicate jacop_strictly_increasing(array[int] of var int: x);

predicate fzn_strictly_increasing_int(array[int] of var int: x) =
   jacop_strictly_increasing(x);
