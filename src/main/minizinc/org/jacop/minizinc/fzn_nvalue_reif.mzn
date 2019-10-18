predicate jacop_nvalue(var int: n, array[int] of var int: x);

predicate fzn_nvalue_reif(var int: n, array[int] of var int: x, var bool: b) =
	  let {
	    var 1..card(index_set(x)): t,
	  } in
	  jacop_nvalue(t, x)
	  /\
	  (b <-> n = t)
	  ;
