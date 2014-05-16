%-----------------------------------------------------------------------------%
% Requires that each item with weight w[i] is put into bin[i] such that
% the sum of weights in each bin b is equal to load l[b].
% Assumptions:
% - forall i, w[i] >= 0
%-----------------------------------------------------------------------------%
include "bin_packing.mzn";

predicate bin_packing_load(array[int] of int: l,
                           array[int] of var int: bin,
                           array[int] of int: w) =
    assert(index_set(bin) == index_set(w),
        "bin_packing_load: the bin and w array arguments must have identical index sets",
    assert(lb_array(w) >= 0,
        "bin_packing_load: the weights must be non-negative",
	 let {
	    set of int: l_index = index_set(l),
	    array [l_index] of var 0..ub_array(l) : load
	 }
	 in 
	    forall (i in index_set(l) ) (load[i] = l[i]) /\
	    jacop_bin_packing(bin, load, w)
	 
    ));
