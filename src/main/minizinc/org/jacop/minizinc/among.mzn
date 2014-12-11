/**  @group globals.counting
  Requires exactly \a n variables in \a x to take one of the values in \a v.
*/
predicate among(var int: n, array[int] of var int: x, set of int: v) =
	  jacop_among(x, v, n);

predicate jacop_among(array[int] of var int: x, set of int: v, var int: n);