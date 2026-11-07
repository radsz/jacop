include "jacop_graph.mzn";

predicate fzn_bounded_dpath(int: N, int: E, array [int] of int: from, array [int] of int: to, array [int] of int: w,
                         var int: s, var int: t, array [int] of var bool: ns, array [int] of var bool: es, var int: K) =
  jacop_bounded_dpath(from, to, w, s, t, ns, es, K, min(index_set(ns)));
