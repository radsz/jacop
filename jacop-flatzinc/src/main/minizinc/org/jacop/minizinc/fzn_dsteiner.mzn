include "jacop_graph.mzn";

predicate fzn_dsteiner(int: N, int: E, array [int] of int: from, array [int] of int: to, array [int] of int: w, var int: r, array [int] of var bool: ns, array [int] of var bool: es, var int: K) =
  jacop_dsteiner(from, to, w, r, ns, es, K, min(index_set(ns)));
