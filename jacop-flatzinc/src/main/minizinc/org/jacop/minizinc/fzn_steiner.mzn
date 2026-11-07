include "jacop_graph.mzn";

predicate fzn_steiner(int: N, int: E, array [int] of int: from, array [int] of int: to, array [int] of int: w, array [int] of var bool: ns, array [int] of var bool: es, var int: K) =
  jacop_steiner(from, to, w, ns, es, K, min(index_set(ns)));
