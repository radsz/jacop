predicate jacop_nvalue(var int: n, array[int] of var int: x);

predicate fzn_nvalue_reif(var int: n, array[int] of var int: x, var bool: b) =
	  let {
	    % an empty x has no value: t = 0 there, and jacop_nvalue gives t >= 1 otherwise
	    var 0..card(index_set(x)): t,
	  } in
	  jacop_nvalue(t, x)
	  /\
	  (b <-> n = t)
	  ;
