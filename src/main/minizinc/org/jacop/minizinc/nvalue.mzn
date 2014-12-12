/** @group globals.alldifferent
  Requires that the number of distinct values in \a x is \a n.
*/
predicate nvalue(var int: n, array[int] of var int: x) =
        jacop_nvalue(n, x);

predicate jacop_nvalue(var int: n, array[int] of var int: x);
