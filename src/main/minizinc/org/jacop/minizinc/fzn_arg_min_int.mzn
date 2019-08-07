predicate jacop_minimum_arg_int(array[int] of var int: x, var int: i);

predicate fzn_minimum_arg_int(array[int] of var int: x, var int: i) =
  jacop_minimum_arg_int(x,i);
