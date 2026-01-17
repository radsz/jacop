%-----------------------------------------------------------------------------%
% Requires at most 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate at_most_int(int: n, array[int] of var int: x, int: v) =
	  jacop_atmost(x, v, n);

predicate at_most_int_reif(int: n, array[int] of var int: x, int: v, var bool: b) =
	   jacop_atmost_reif(x, v, n, b);

predicate jacop_atmost(array[int] of var int: x, int: v, int: n);
predicate jacop_atmost_reif(array[int] of var int: x, int: v, int: n, var bool: b);
