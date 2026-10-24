predicate jacop_bin_packing(array[int] of var int: bin, array[int] of var int: cap, array[int] of int: w, int: min_bin);

predicate fzn_bin_packing_load(array[int] of var int: load,
                           array[int] of var int: bin,
                           array[int] of int: w) =
         jacop_bin_packing(bin, load, w, min(index_set(load))) %% lb_array(bin))
    ;

%-----------------------------------------------------------------------------%
