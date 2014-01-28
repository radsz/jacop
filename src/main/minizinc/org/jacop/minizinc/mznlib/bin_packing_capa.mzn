%-----------------------------------------------------------------------------%
% Requires that each item with weight w[i] is put into bin[i] such that
% the sum of weights in each bin b does not exceed capacity c[b].
% Assumptions:
% - forall i, w[i] >= 0
%-----------------------------------------------------------------------------%
include "bin_packing.mzn";

predicate bin_packing_capa(array[int] of int: c,
                           array[int] of var int: bin,
                           array[int] of int: w) =
    assert(index_set(bin) == index_set(w),
        "bin_packing_capa: the bin and w array arguments must have identical index sets",
    assert(lb_array(w) >= 0,
        "bin_packing_capa: the weights must be non-negative",
	 let {
	    set of int: lc = index_set(c),
	    array [lc] of var 0..ub_array(c) : cap
	 }
	 in 
	    forall (i in index_set(c) ) ( cap[i] <= c[i]) /\
	    jacop_bin_packing(bin, cap, w)

    ));
