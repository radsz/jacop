predicate jacop_clique(array[int,int] of int: graph, array[int] of var bool: c, int: lb);

predicate fzn_clique(array[int,int] of int: graph, array[int] of var bool: c, int: lc) =
   let {
      int: e_min = min(index_set_2of2(graph)),
      int: e_max = max(index_set_2of2(graph)),
   } in
   assert(e_max - e_min = 1,
          "wrong specification of the graph",
    jacop_clique(graph, c, lc)
    );
