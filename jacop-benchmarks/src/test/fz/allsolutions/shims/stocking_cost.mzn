include "all_different.mzn";
include "global_cardinality.mzn";
predicate stocking_cost(array[int] of var int: x, array[int] of int: d,
                        array[int] of int: h, var int: cost, int: c) =
    forall(i in index_set(x))(x[i] <= d[i]) /\
    forall(t in lb_array(x)..ub_array(x))(sum(i in index_set(x))(bool2int(x[i] = t)) <= c) /\
    cost = sum(i in index_set(x))(h[i] * (d[i] - x[i]));
predicate stocking_cost(array[int] of var int: x, array[int] of int: d, var int: cost, int: c) =
    stocking_cost(x, d, [1 | i in index_set(x)], cost, c);
