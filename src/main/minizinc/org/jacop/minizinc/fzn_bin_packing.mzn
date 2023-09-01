predicate jacop_bin_packing_capacity(array[int] of var int: bin, array[int] of int: cap, array[int] of int: w, int: min_bin);

predicate fzn_bin_packing(int: c,
                      array[int] of var int: bin,
                      array[int] of int: w) =
	 let {
	   set of int: cap_index = lb_array(bin)..ub_array(bin),
	   array[cap_index] of int: cap = [c | i in cap_index];
	 }
	 in 
        jacop_bin_packing_capacity(bin, cap, w, lb_array(bin))
    ;
