predicate jacop_minimum_arg_int(array[int] of var int: x, var int: i, int: offset);

predicate fzn_minimum_arg_int(array[int] of var int: x, var int: i) =
  jacop_minimum_arg_int(x,i,min(index_set(x)));
