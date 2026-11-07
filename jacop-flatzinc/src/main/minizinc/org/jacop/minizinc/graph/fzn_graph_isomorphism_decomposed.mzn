include "all_different.mzn";

predicate fzn_graph_isomorphism_decomposed(array[int] of set of int: target_graph, array[int] of set of int: pattern_graph,
                                       array[int] of int: target_type, array[int] of int: pattern_type,
                                       array[int] of var int: match) =
      all_different(match) :: domain
      /\
      forall (i in index_set(match)) (pattern_type[i] = target_type[match[i]])
      /\
      forall (i,j in index_set(match) where i != j) (match[j] in target_graph[match[i]] <-> j in pattern_graph[i])
;
