include "all_different.mzn";
include "global_cardinality.mzn";

/** @doc Constrains order i to be produced in period x[i], at the latest on its due date d[i],
  with at most c orders produced in the same period, and cost to be the stocking cost
  sum(i in index_set(x))(h[i] * (d[i] - x[i])). JaCoP's StockingCost constraint (Houndji et al.,
  CP 2014 and Constraints 2019) bounds the cost from the capacity and raises the earliest periods
  that the maximum of the cost allows. The predicate is specific to JaCoP; for other solvers the
  body without jacop_stocking_cost is its decomposition.
*/
predicate stocking_cost(array[int] of var int: x, array[int] of int: d,
                        array[int] of int: h, var int: cost, int: c) =
    assert(index_set(x) = index_set(d) /\ index_set(x) = index_set(h),
           "stocking_cost: x, d and h must have the same index set") /\
    assert(c >= 1, "stocking_cost: the capacity c must be at least 1") /\
    assert(forall(i in index_set(h))(h[i] >= 0), "stocking_cost: the costs h must be at least 0") /\
    forall(i in index_set(x))(x[i] <= d[i]) /\
    if c = 1 then
      all_different(x)
    else
      let { set of int: periods = lb_array(x)..ub_array(x) } in
      global_cardinality(x, [t | t in periods], [0 | t in periods], [c | t in periods])
    endif /\
    cost = sum(i in index_set(x))(h[i] * (d[i] - x[i])) /\
    jacop_stocking_cost(x, d, h, cost, c);

/** @doc Constrains order i to be produced in period x[i] at the latest on its due date d[i],
  at most c orders per period, and cost to be the number of periods between the production
  periods and the due dates.
*/
predicate stocking_cost(array[int] of var int: x, array[int] of int: d, var int: cost, int: c) =
    stocking_cost(x, d, [1 | i in index_set(x)], cost, c);

predicate jacop_stocking_cost(array[int] of var int: x, array[int] of int: d,
                              array[int] of int: h, var int: cost, int: c);
