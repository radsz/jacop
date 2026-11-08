include "subcircuit.mzn";
predicate subcircuit_cost(array[int] of var int: x, array[int,int] of int: d, var int: cost) =
  subcircuit(x) /\ cost = sum(i in index_set(x))(d[i, x[i]]);
