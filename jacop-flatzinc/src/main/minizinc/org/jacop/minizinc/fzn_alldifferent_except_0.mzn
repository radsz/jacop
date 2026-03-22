predicate jacop_alldifferent_except_0(array[int] of var int: vs);

predicate fzn_alldifferent_except_0(array[int] of var int: vs) =
    jacop_alldifferent_except_0(vs);
