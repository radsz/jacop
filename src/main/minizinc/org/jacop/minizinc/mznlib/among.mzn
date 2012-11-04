%-----------------------------------------------------------------------------%
% Requires exactly 'n' variables in 'x' to take one of the values in 'v'.
%-----------------------------------------------------------------------------%
predicate among(var int: n, array[int] of var int: x, set of int: v) =
	  jacop_among(x, v, n);

%    n == sum(i in index_set(x)) ( bool2int(x[i] in v) );

predicate jacop_among(array[int] of var int: x, set of int: v, var int: n);