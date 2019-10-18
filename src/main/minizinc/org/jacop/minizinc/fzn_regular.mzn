predicate jacop_regular(array[int] of var int: x, int: Q, int: S,
                        array[int, int] of int: d, int: q0, set of int: F, int: min_index);

predicate fzn_regular(array[int] of var int: x, int: Q, int: S,
                  array[int,int] of int: d, int: q0, set of int: F) =
	  jacop_regular(x, Q, S, d, q0, F,  min(index_set_2of2(d)))

    ;
