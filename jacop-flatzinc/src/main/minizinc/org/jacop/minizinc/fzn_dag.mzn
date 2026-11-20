include "jacop_graph.mzn";

predicate fzn_dag(array [int] of int: from, array [int] of int: to, array [int] of var bool: ns, array [int] of var bool: es) =
  jacop_dag(from, to, ns, es, min(index_set(ns)));
