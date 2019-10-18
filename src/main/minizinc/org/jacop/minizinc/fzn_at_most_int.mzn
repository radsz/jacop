predicate jacop_atmost(array[int] of var int: x, int: v, int: n);

predicate fzn_at_most_int(int: n, array[int] of var int: x, int: v) =
	  jacop_atmost(x, v, n);


