include "graph/fzn_sub_digraph_match.mzn";
include "graph/fzn_sub_digraph_match_decomposed.mzn";

predicate sub_digraph_match(array[int,int] of int: target, array[int,int] of int: pattern,
			    array[int] of int: target_node_type, array[int] of int: pattern_node_type, array[int] of var int: match) =
    let { int: lt2 = min(index_set_2of2(target)),
          int: ut2 = max(index_set_2of2(target)),
          int : st2 = (ut2 - lt2 + 1),
	  int: lp2 = min(index_set_2of2(pattern)),
          int: up2 = max(index_set_2of2(pattern)),
          int : sp2 = (up2 - lp2 + 1),
	  int: lp = min(index_set_1of2(pattern)),
	  int: lm = min(index_set(match))
	}
        in
        
	  assert( st2 = 2 /\  sp2 = 2 /\ lm = lp,
	    "graph_match: size of an edge must be 2 and min index of target, patter and match must be equal",
                  if use_jacop_graph_constraints == true then
		      fzn_sub_digraph_match(target, pattern, target_node_type, pattern_node_type, match, lm)
                  else
		      fzn_sub_digraph_match_decomposed(target, pattern, target_node_type, pattern_node_type, match)
                  endif
                  
	  );

predicate sub_digraph_match(array[int,int] of int: target, array[int,int] of int: pattern, array[int] of var int: match) =
    sub_digraph_match(target, pattern,
                      array1d(lb_array(target)..ub_array(target), [1 | i in lb_array(target)..ub_array(target)]),
                      array1d(index_set(match), [1 | i in index_set(match)]), match);

