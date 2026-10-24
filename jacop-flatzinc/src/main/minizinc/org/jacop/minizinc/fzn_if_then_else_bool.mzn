predicate jacop_if_then_else_bool(array[int] of var bool: c, array[int] of bool: x, var bool: y);

predicate fzn_if_then_else_bool(array[int] of var bool: c, array[int] of bool: x, var bool: y) =
  jacop_if_then_else_bool(c, x, y);
