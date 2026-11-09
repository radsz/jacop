% JaCoP's GCC(x, c): c[i] counts value i and x takes only counted values.
include "global_cardinality_closed.mzn";
predicate GCC(array[int] of var int: x, array[int] of var int: c) =
  global_cardinality_closed(x, [i | i in index_set(c)], [c[i] | i in index_set(c)]);
