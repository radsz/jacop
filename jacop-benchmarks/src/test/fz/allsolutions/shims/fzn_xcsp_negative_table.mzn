% x matches no row of t
predicate fzn_xcsp_negative_table(array[int] of var int: x, array[int, int] of int: t) =
  forall(i in index_set_1of2(t))(exists(j in index_set(x))(x[j] != t[i, j]));
