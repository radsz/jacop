predicate jacop_atleast_reif(array[int] of var int: x, int: v, int: n, var bool: b);

predicate fzn_count_lt_par_reif(array[int] of var int: x, int: y, int: c, var bool: b) =
   jacop_atleast_reif(x, y, c + 1, b);
