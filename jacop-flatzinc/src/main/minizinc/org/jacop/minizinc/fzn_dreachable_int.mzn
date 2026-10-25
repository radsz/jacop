include "jacop_graph.mzn";

predicate fzn_dreachable(int: N, int: E, array [int] of int: from, array [int] of int: to, var int: r, array [int] of var bool: ns, array [int] of var bool: es) =
  jacop_dreachable(from, to, r, ns, es, min(index_set(ns)));
