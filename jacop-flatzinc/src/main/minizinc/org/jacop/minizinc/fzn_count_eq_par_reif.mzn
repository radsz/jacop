predicate jacop_count_reif(array[int] of var int: x, int: y, var int: c, var bool: b);

predicate fzn_count_eq_par_reif(array[int] of var int: x, int: y, int: c, var bool: b) =
    jacop_count_reif(x, y, c, b);

%-----------------------------------------------------------------------------%
