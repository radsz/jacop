% x matches one row of t, where the value star matches any value
predicate fzn_xcsp_short_table(array[int] of var int: x, array[int, int] of int: t, int: star) =
  exists(i in index_set_1of2(t))(forall(j in index_set(x))(t[i, j] = star \/ x[j] = t[i, j]));
