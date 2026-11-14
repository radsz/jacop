include "fzn_count_eq.mzn";

predicate fzn_exactly_int(int: n, array[int] of var int: x, int: v) =
	  fzn_count_eq(x, v, n);
