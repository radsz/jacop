predicate jacop_value_precede_int(int: s, int: t, array[int] of var int: x);

predicate fzn_value_precede_int(int: s, int: t, array[int] of var int: x) =
	  jacop_value_precede_int(s, t, x);
