predicate jacop_among(array[int] of var int: x, set of int: v, var int: n);

predicate fzn_among_reif(var int: n, array[int] of var int: x, set of int: v, var bool: b) =
	  let { 
          int: l = min(index_set(x)),
          int: u = max(index_set(x)),
	  int: mm = u - l + 1, 
	  var 0..mm: ni
	  }
	  in
	  jacop_among(x, v, ni)
	  /\
	  (b <-> ni = n)
;
