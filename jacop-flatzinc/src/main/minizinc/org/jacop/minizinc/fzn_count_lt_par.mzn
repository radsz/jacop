predicate jacop_atleast(array[int] of var int: x, int: v, int: n);

predicate fzn_count_lt_par(array[int] of var int: x, int: y, int: c) =
    jacop_atleast(x, y, c + 1);

%-----------------------------------------------------------------------------%
