predicate jacop_count_values(array[int] of var int: x,
			     array[int] of int: cover,
			     array[int] of var int: counter);

predicate fzn_global_cardinality(array[int] of var int: x,
	  		     array[int] of int: cover,
                             array[int] of var int: counts) =
    jacop_count_values(x, cover, counts);
