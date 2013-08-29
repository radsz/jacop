%-----------------------------------------------------------------------------%
% Requires that each item with weight w[i] is put into bin[i] such that
% the sum of weights in each bin b is equal to load l[b].
% Assumptions:
% - forall i, w[i] >= 0
%-----------------------------------------------------------------------------%
predicate bin_packing_jacop(array[int] of var int: l,
                           array[int] of var int: bin,
                           array[int] of int: w) =
    assert(index_set(bin) == index_set(w),
        "bin_packing_load: the bin and w array arguments must have identical index sets",
    assert(lb_array(w) >= 0,
        "bin_packing_load: the weights must be non-negative",

	 jacop_bin_packing(bin, l, w)
	 
    ));
