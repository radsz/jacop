predicate jacop_maximum_arg_int(array[int] of var int: x, var int: i);

predicate fzn_maximum_arg_int(array[int] of var int: x, var int: i) =
  jacop_maximum_arg_int(x,i);


