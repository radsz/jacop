/** @doc Constrains every value to occur in y at most as often as in x: the values of y are a
  sub-multiset of the values of x (used_by of the Global Constraint Catalog). JaCoP's UsedBy
  constraint is domain consistent, with the flow network of Beldiceanu, Katriel and Thiel,
  "Filtering algorithms for the Same and UsedBy constraints", MPI-I-2004-1-001. The predicate is
  specific to JaCoP.
*/
predicate used_by(array[int] of var int: x, array[int] of var int: y) =
    assert(length(y) <= length(x), "used_by: y cannot be longer than x") /\
    jacop_used_by(x, y);

predicate jacop_used_by(array[int] of var int: x, array[int] of var int: y);
