predicate jacop_bin_packing(array[int] of var int: bin, array[int] of var int: cap, array[int] of int: w, int: min_bin);

predicate fzn_bin_packing_capa(array[int] of int: c,
                           array[int] of var int: bin,
                           array[int] of int: w) =
	 let {
	    set of int: lc = index_set(c),
	    array [lc] of var 0..ub_array(c) : cap
	 }
	 in 
	    forall (i in index_set(c) ) ( cap[i] <= c[i]) /\
	    jacop_bin_packing(bin, cap, w, lb_array(bin))
    ;
