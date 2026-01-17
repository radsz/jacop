include "all_different.mzn";

predicate fzn_sub_graph_match_decomposed(array[int,int] of int: target_graph, array[int,int] of int: pattern_graph,
                                         array[int] of int: target_type, array[int] of int: pattern_type,
                                         array[int] of var int: match) =
   let {
      set of int: index_set_edges = index_set_1of2(target_graph),
      int: t1_min = lb_array(target_graph),
      int: t1_max = ub_array(target_graph),
      int: t2_min = min(index_set_2of2(target_graph)),
      int: t2_max = max(index_set_2of2(target_graph)),
      array[t1_min..t1_max] of set of int: et = array1d(t1_min..t1_max, [ {target_graph[j,t2_max] | j in index_set_edges where target_graph[j,t2_min] = i}
                                                 union {target_graph[j,t2_min] | j in index_set_edges where target_graph[j,t2_max] = i} | i in t1_min..t1_max]),

      set of int: index_set_p_edges = index_set_1of2(pattern_graph),
      int: p1_min = lb_array(pattern_graph),
      int: p1_max = ub_array(pattern_graph),
      int: p2_min = min(index_set_2of2(pattern_graph)),
      int: p2_max = max(index_set_2of2(pattern_graph)),
      array[p1_min..p1_max] of set of int: pt = array1d(p1_min..p1_max, [ {pattern_graph[j,p2_max] | j in index_set_p_edges where pattern_graph[j,p2_min] = i}
                                                 union {pattern_graph[j,p2_min] | j in index_set_p_edges where pattern_graph[j,p2_max] = i} | i in p1_min..p1_max]),
   } in
      all_different(match) :: domain
      /\
      forall (i in index_set(match)) (pattern_type[i] = target_type[match[i]])
      /\
      % forall (i in index_set(match), j in pt[i]) (match[j] in et[match[i]])  %% monomorphism condition
      % /\
      forall (i,j in index_set(match) where i != j) (match[j] in et[match[i]] <-> j in pt[i])  %% isomorphism constraint
;
