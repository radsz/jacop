predicate jacop_alldiff(array[int] of var int: x);

predicate fzn_all_different_int(array[int] of var int: x) =
	  jacop_alldiff(x);
