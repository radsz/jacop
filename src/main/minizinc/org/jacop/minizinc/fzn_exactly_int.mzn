include "fzn_count.mzn";

predicate fzn_exactly_int(int: n, array[int] of var int: x, int: v) =
	  fzn_count(x, v, n);
