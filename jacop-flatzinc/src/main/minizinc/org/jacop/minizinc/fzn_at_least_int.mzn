predicate jacop_atleast(array[int] of var int: x, int: v, int: n);

predicate fzn_at_least_int(int: n, array[int] of var int: x, int: v) =
	jacop_atleast(x, v, n);


