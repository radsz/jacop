predicate fzn_table_bool_imp(array[int] of var bool: x, array[int, int] of bool: t, var bool: b) =
  b -> exists(r in index_set_1of2(t))(forall(j in index_set(x))(x[j] = t[r, j]));
