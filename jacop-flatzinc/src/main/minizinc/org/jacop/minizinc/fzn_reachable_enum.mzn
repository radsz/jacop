include "jacop_graph.mzn";

predicate fzn_reachable(array [int] of int: from, array [int] of int: to, var int: r, array [int] of var bool: ns, array [int] of var bool: es) =
  jacop_reachable(from, to, r, ns, es, min(index_set(ns)));
