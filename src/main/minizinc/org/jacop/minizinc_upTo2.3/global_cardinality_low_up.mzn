/** @group globals.counting
  Requires that for all \p i, the value \a cover[\p i] appears at least \a lbound[\p i]
  and at most \a ubound[\p i] times in the array \a x.
*/

predicate global_cardinality_low_up(array[int] of var int: x,
                                    array[int] of int: cover,
                                    array[int] of int: lbound,
                                    array[int] of int: ubound) =
     forall(i in index_set(cover)) (
       jacop_count_bounds(x, cover[i], lbound[i], ubound[i])
     );

predicate jacop_count_bounds(array[int] of var int: x, int: cover, int: lbound, int: ubound)