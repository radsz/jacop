%-----------------------------------------------------------------------------%
% Requires at least 'n' variables in 'x' to take the value 'v'.
%-----------------------------------------------------------------------------%

predicate at_least_int(int: n, array[int] of var int: x, int: v) =
	jacop_atleast(x, v, n);

predicate at_least_int_reif(int: n, array[int] of var int: x, int: v, var bool: b) =
	  jacop_atleast_reif(x, v, n, b);

predicate jacop_atleast(array[int] of var int: x, int: v, int: n);
predicate jacop_atleast_reif(array[int] of var int: x, int: v, int: n, var bool: b);

