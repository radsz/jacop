include "jacop_graph.mzn";

predicate fzn_dwst(int: N, int: E, array [int] of int: from, array [int] of int: to, array [int] of int: w, var int: r,
                   array [int] of var bool: es, var int: K) =
  jacop_dwst(N, from, to, w, r, es, K);
