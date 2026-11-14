include "jacop_graph.mzn";

predicate fzn_path(array [int] of int: from, array [int] of int: to, var int: s, var int: t, array [int] of var bool: ns, array [int] of var bool: es) =
  jacop_path(from, to, s, t, ns, es, min(index_set(ns)));
