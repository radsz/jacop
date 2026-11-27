%-----------------------------------------------------------------------------%
% Requires exactly 'n' variables in 'x' to take one of the values in 'v'.
%-----------------------------------------------------------------------------%
predicate among_var(var int: n, array[int] of var int: x, array[int] of var int: v) =
	  jacop_among_var(x, v, n);

predicate jacop_among_var(array[int] of var int: x, array[int] of var int: v, var int: n);


%-----------------------------------------------------------------------------%
% Reified version of among_var.
%-----------------------------------------------------------------------------%
predicate among_var_reif(var int: n, array[int] of var int: x, array[int] of var int: v, var bool: b) =
	  let { 
	  % length(x), not max - min + 1: min(index_set(x)) is undefined for an empty x
	  int: mm = length(x), 
	  var 0..mm: ni
	  }
	  in
	  jacop_among_var(x, v, ni)
	  /\
	  (b <-> ni = n)
;
