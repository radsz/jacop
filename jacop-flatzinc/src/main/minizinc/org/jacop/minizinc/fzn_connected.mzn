include "jacop_graph.mzn";

predicate fzn_connected(array [int] of int: from, array [int] of int: to, array [int] of var bool: ns, array [int] of var bool: es) =
  jacop_connected(from, to, ns, es, min(index_set(ns)));
