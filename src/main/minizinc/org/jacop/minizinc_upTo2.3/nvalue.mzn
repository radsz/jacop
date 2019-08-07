/** @group globals.alldifferent
  Requires that the number of distinct values in \a x is \a n.
*/
predicate nvalue(var int: n, array[int] of var int: x) =
        jacop_nvalue(n, x);

predicate jacop_nvalue(var int: n, array[int] of var int: x);

predicate jacop_nvalue_reif(var int: n, array[int] of var int: x, var bool: b) =
	  let {
	    var 1..card(index_set(x)): t,
	  } in
	  jacop_nvalue(t, x)
	  /\
	  (b <-> n = t)
	  ;
