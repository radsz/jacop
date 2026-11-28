predicate jacop_among(array[int] of var int: x, set of int: v, var int: n);

predicate fzn_among_reif(var int: n, array[int] of var int: x, set of int: v, var bool: b) =
	  let { 
	  % length(x), not max - min + 1: min(index_set(x)) is undefined for an empty x
	  int: mm = length(x), 
	  var 0..mm: ni
	  }
	  in
	  jacop_among(x, v, ni)
	  /\
	  (b <-> ni = n)
;
