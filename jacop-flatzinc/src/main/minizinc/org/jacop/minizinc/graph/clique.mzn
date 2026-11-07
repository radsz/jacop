include "graph/fzn_clique.mzn";
include "graph/fzn_clique_decomposed.mzn";

predicate clique(array[int,int] of int: graph, array[int] of var bool: c) =
     let { int: lg = min(index_set_1of2(graph)),
	   int: lc = min(index_set(c))
         } in
	 assert(lg = lc,
		"clique: min index of graph and c must be equal",
         if use_jacop_graph_constraints == true then
           fzn_clique(graph, c, lc)
         else
           fzn_clique_decomposed(graph, c)
           endif
	 );
