predicate jacop_alldifferent_except(array[int] of var int: vs, set of int: S);

predicate fzn_alldifferent_except(array[int] of var int: vs, set of int: S) =
    jacop_alldifferent_except(vs,S);
