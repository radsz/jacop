predicate jacop_minimum_arg_bool(array[int] of var bool: x, var int: i, int: offset);

predicate fzn_minimum_arg_bool(array[int] of var bool: x, var int: i) =
  jacop_minimum_arg_bool(x,i,min(index_set(x)));
