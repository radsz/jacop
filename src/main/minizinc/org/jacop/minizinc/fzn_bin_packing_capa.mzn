predicate jacop_bin_packing_capacity(array[int] of var int: bin, array[int] of int: cap, array[int] of int: w, int: min_bin);

predicate fzn_bin_packing_capa(array[int] of int: c,
                           array[int] of var int: bin,
                           array[int] of int: w) =
       jacop_bin_packing_capacity(bin, c, w, lb_array(bin))
    ;
