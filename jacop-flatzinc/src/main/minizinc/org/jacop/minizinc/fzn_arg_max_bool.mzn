predicate jacop_maximum_arg_bool(array[int] of var bool: x, var int: i, int: offset);

predicate fzn_maximum_arg_bool(array[int] of var bool: x, var int: i) =
  jacop_maximum_arg_bool(x,i,min(index_set(x)));


