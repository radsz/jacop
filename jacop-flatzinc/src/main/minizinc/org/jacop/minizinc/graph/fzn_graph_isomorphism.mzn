predicate jacop_graph_isomorphism(array[int] of set of int: target, array[int] of set of int: pattern,
				  array[int] of int: target_type, array[int] of int: pattern_type,
				  array[int] of var int: map, int: offset);


predicate fzn_graph_isomorphism(array[int] of set of int: target, array[int] of set of int: pattern,
			    array[int] of int: target_type, array[int] of int: pattern_type,
			    array[int] of var int: map) =
    jacop_graph_isomorphism(target, pattern, target_type, pattern_type, map, min(index_set(map)) - 1);
