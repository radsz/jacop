%-----------------------------------------------------------------------------%
% Requires that the array 'x' is in increasing order
%-----------------------------------------------------------------------------%
predicate jacop_increasing(array[int] of var int: x);

predicate fzn_increasing_int(array[int] of var int: x) =
   jacop_increasing(x);
