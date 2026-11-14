predicate fzn_clique_decomposed(array[int,int] of int: a, array[int] of var bool: c) =
   let {
      set of int: index_set_edges = index_set_1of2(a),
      int: n_min = lb_array(a),
      int: n_max = ub_array(a),
      int: e_min = min(index_set_2of2(a)),
      int: e_max = max(index_set_2of2(a)),
      array[n_min..n_max] of set of int: e = array1d(n_min..n_max, [ {a[j,e_max] | j in index_set_edges where a[j,e_min] = i} union {a[j,e_min] | j in index_set_edges where a[j,e_max] = i} | i in n_min..n_max]),
   } in
   assert(e_max - e_min = 1,
          "wrong specification of the graph",
          forall (i in n_min..n_max, j in n_min..n_max where i != j) (if not(j in e[i]) then c[i] != true \/ c[j] != true else true endif)
   );
