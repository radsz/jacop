include "jacop_graph.mzn";

predicate fzn_wst(int: N, int: E, array [int] of int: from, array [int] of int: to, array [int] of int: w,
                  array [int] of var bool: es, var int: K) =
  jacop_wst(N, from, to, w, es, K);
