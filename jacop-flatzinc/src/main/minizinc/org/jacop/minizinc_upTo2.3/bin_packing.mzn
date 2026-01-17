/**  @group globals.packing
  Requires that each item \p i with weight \a w[\p i], be put into \a bin[\p i] such 
  that the sum of the weights of the items in each bin does not exceed the 
  capacity \a c.

  Assumptions:
  - forall \p i, \a w[\p i] >=0
  - \a c >=0
*/
predicate bin_packing(int: c,
                      array[int] of var int: bin,
                      array[int] of int: w) =
    assert(index_set(bin) == index_set(w),
        "bin_packing: the array arguments must have identical index sets",
    assert(lb_array(w) >= 0,
        "bin_packing: the weights must be non-negative",
	 let {
	   set of int: cap_index = lb_array(bin)..ub_array(bin),
	   array[cap_index] of var 0..c: cap
	 }
	 in 
	   jacop_bin_packing(bin, cap, w, lb_array(bin))
    ));

predicate jacop_bin_packing(array[int] of var int: bin, array[int] of var int: cap, array[int] of int: w, int: min_bin);

% predicate jacop_bin_packing_reif(array[int] of var int: bin, array[int] of var int: cap, array[int] of int: w, int: min_bin, var bool: b) =
%     abort("Reified bin_packing/3 is not supported.");
