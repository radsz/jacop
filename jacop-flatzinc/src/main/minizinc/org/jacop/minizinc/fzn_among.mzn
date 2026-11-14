predicate jacop_among(array[int] of var int: x, set of int: v, var int: n);

predicate fzn_among(var int: n, array[int] of var int: x, set of int: v) =
	  jacop_among(x, v, n);
