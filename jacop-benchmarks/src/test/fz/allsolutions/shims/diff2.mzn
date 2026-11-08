predicate diff2(array[int,int] of var int: r) =
  forall(i, j in index_set_1of2(r) where i < j)(
    r[i, 1] + r[i, 3] <= r[j, 1] \/ r[j, 1] + r[j, 3] <= r[i, 1] \/
    r[i, 2] + r[i, 4] <= r[j, 2] \/ r[j, 2] + r[j, 4] <= r[i, 2]);
predicate diff2(array[int] of var int: x, array[int] of var int: y,
                array[int] of var int: lx, array[int] of var int: ly) =
  forall(i, j in index_set(x) where i < j)(
    x[i] + lx[i] <= x[j] \/ x[j] + lx[j] <= x[i] \/
    y[i] + ly[i] <= y[j] \/ y[j] + ly[j] <= y[i]);
