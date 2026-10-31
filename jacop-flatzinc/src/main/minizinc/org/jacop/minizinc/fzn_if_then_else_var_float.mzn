predicate jacop_if_then_else_float(array[int] of var bool: c, array[int] of var float: x, var float: y);

predicate fzn_if_then_else_var_float(array[int] of var bool: c, array[int] of var float: x, var float: y) =
  jacop_if_then_else_float(c, x, y);
