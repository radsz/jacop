/** @doc Constrains y to be a permutation of x: both arrays hold the same multiset of values
  (same of the Global Constraint Catalog). JaCoP's Same constraint is domain consistent, with the
  flow network of Beldiceanu, Katriel and Thiel, "Filtering algorithms for the Same constraint",
  CPAIOR 2004. The predicate is specific to JaCoP.
*/
predicate same(array[int] of var int: x, array[int] of var int: y) =
    assert(length(x) = length(y), "same: x and y must have the same length") /\
    jacop_same(x, y);

predicate jacop_same(array[int] of var int: x, array[int] of var int: y);
