predicate jacop_all_disjoint(array[int] of var set of int: S);

predicate fzn_all_disjoint(array[int] of var set of int: S) =
    jacop_all_disjoint(S);
