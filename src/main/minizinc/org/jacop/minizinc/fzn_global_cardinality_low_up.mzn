predicate jacop_count_values_bounds(array[int] of var int: x,
				    array[int] of int: cover,
				    array[int] of int: lbound,
				    array[int] of int: ubound);

predicate fzn_global_cardinality_low_up(array[int] of var int: x,
                                    array[int] of int: cover,
                                    array[int] of int: lbound,
                                    array[int] of int: ubound) =
   jacop_count_values_bounds(x, cover, lbound, ubound);
