predicate jacop_count_values_bounds(array[int] of var int: x,
				    array[int] of int: cover,
				    array[int] of int: lbound,
				    array[int] of int: ubound);

predicate fzn_global_cardinality_low_up_closed(array[int] of var int: x,
                                           array[int] of int: cover,
				           array[int] of int: lbound,
                                           array[int] of int: ubound) =
     % closed: every variable takes a value from cover
     forall(i in index_set(x))(x[i] in {d | d in cover})
     /\
     jacop_count_values_bounds(x, cover, lbound, ubound);
