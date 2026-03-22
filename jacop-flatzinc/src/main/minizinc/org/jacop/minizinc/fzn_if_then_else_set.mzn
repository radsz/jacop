predicate jacop_if_then_else_set(array[int] of var bool: c, array[int] of set of int: x, var set of int: y);

predicate fzn_if_then_else_set(array[int] of var bool: c, array[int] of set of int: x, var set of int: y) =
  jacop_if_then_else_set(c, x, y);
