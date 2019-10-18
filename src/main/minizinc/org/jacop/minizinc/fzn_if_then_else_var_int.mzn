predicate jacop_if_then_else_int(array[int] of var bool: c, array[int] of var int: x, var int: y);

predicate fzn_if_then_else_var_int(array[int] of var bool: c, array[int] of var int: x, var int: y) =
  jacop_if_then_else_int(c, x, y);
