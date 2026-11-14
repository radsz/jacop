predicate jacop_partition_set(array[int] of var set of int: S,
                              set of int: universe);

predicate fzn_partition_set(array[int] of var set of int: S,
                            set of int: universe) =
    jacop_partition_set(S, universe);
