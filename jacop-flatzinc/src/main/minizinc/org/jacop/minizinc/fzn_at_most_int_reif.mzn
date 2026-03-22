predicate jacop_atmost_reif(array[int] of var int: x, int: v, int: n, var bool: b);

predicate fzn_at_most_int_reif(int: n, array[int] of var int: x, int: v, var bool: b) =
	   jacop_atmost_reif(x, v, n, b);
