predicate jacop_sub_graph_match(array[int,int] of int: target, array[int,int] of int: pattern,
				array[int] of int: target_node_type, array[int] of int: pattern_node_type, array[int] of var int: match, int: min_index);

predicate fzn_sub_graph_match(array[int,int] of int: target, array[int,int] of int: pattern,
                              array[int] of int: target_node_type, array[int] of int: pattern_node_type, array[int] of var int: match, int: lm) =
     jacop_sub_graph_match(target, pattern, target_node_type, pattern_node_type, match, lm)

