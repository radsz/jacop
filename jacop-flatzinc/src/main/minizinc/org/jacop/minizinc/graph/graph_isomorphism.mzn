include "graph/fzn_graph_isomorphism.mzn";
include "graph/fzn_graph_isomorphism_decomposed.mzn";

predicate graph_isomorphism(array[int] of set of int: target, array[int] of set of int: pattern,
			    array[int] of int: target_type, array[int] of int: pattern_type,
			    array[int] of var int: map) =
assert(length(target) = length(target_type) /\ length(pattern) = length(pattern_type) /\ length(map) = length(pattern),
	      "graph_isomorphism: size of pattern and match as target/pattern and their types must be equal",
                if use_jacop_graph_constraints == true then
                    fzn_graph_isomorphism(target, pattern, target_type, pattern_type, map)
                else
                    fzn_graph_isomorphism_decomposed(target, pattern, target_type, pattern_type, map)
                endif
           );
  
predicate graph_isomorphism(array[int] of set of int: target,
                            array[int] of set of int: pattern,
                            array[int] of var int: map) =
    graph_isomorphism(target, pattern,
                      array1d(index_set(target), [1 | i in index_set(target)]),
                      array1d(index_set(pattern), [1 | i in index_set(pattern)]), map);

predicate graph_isomorphism(array[int,int ] of int: target, array[int,int] of int: pattern,
			    array[int] of int: target_type, array[int] of int: pattern_type,
			    array[int] of var int: map) =
     let {
        set of int: index_set_target_edges = index_set_1of2(target),
        int: t_min = lb_array(target),
        int: t_max = ub_array(target),
        int: t2_min = min(index_set_2of2(target)),
        int: t2_max = max(index_set_2of2(target)),
        array[t_min..t_max] of set of int: et = array1d(t_min..t_max, [ {target[j,t2_max] | j in index_set_target_edges where target[j,t2_min] = i} | i in t_min..t_max]),

        set of int: index_set_pattern_edges = index_set_1of2(pattern),
        int: p_min = lb_array(pattern),
        int: p_max = ub_array(pattern),
        int: p2_min = min(index_set_2of2(target)),
        int: p2_max = max(index_set_2of2(target)),
        array[p_min..p_max] of set of int: pt = array1d(p_min..p_max, [ {pattern[j,p2_max] | j in index_set_pattern_edges where pattern[j,p2_min] = i} | i in p_min..p_max])
     } in
     graph_isomorphism(et, pt, target_type, pattern_type, map);

predicate graph_isomorphism(array[int,int ] of int: target, array[int,int] of int: pattern,
			    array[int] of var int: map) =
     let {
        set of int: index_set_target_edges = index_set_1of2(target),
        int: t_min = lb_array(target),
        int: t_max = ub_array(target),
        int: t2_min = min(index_set_2of2(target)),
        int: t2_max = max(index_set_2of2(target)),
        array[t_min..t_max] of set of int: et = array1d(t_min..t_max, [ {target[j,t2_max] | j in index_set_target_edges where target[j,t2_min] = i} | i in t_min..t_max]),

        set of int: index_set_pattern_edges = index_set_1of2(pattern),
        int: p_min = lb_array(pattern),
        int: p_max = ub_array(pattern),
        int: p2_min = min(index_set_2of2(pattern)),
        int: p2_max = max(index_set_2of2(pattern)),
        array[p_min..p_max] of set of int: pt = array1d(p_min..p_max, [ {pattern[j,p2_max] | j in index_set_pattern_edges where pattern[j,p2_min] = i} | i in p_min..p_max])
     } in
     graph_isomorphism(et, pt, map);
