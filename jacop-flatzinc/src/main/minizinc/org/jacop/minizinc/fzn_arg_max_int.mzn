predicate jacop_maximum_arg_int(array[int] of var int: x, var int: i, int: offset);

predicate fzn_maximum_arg_int(array[int] of var int: x, var int: i) =
  jacop_maximum_arg_int(x,i,min(index_set(x)));


