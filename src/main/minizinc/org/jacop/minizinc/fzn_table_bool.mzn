predicate jacop_table_bool(array[int] of var bool: x, array[int, int] of bool: t);

predicate fzn_table_bool(array[int] of var bool: x, array[int, int] of bool: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
	 jacop_table_bool(x, t)
    );
