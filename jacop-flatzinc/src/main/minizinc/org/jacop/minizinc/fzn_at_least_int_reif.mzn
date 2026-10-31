predicate jacop_atleast_reif(array[int] of var int: x, int: v, int: n, var bool: b);

predicate fzn_at_least_int_reif(int: n, array[int] of var int: x, int: v, var bool: b) =
	  jacop_atleast_reif(x, v, n, b);
