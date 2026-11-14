predicate jacop_table_bool_reif(array[int] of var bool: x, array[int] of bool: t, var bool: b);

predicate fzn_table_bool_reif(array[int] of var bool: x, array[int, int] of bool: t, var bool: b) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            jacop_table_bool_reif(x, array1d(t), b)
    );

predicate jacop_table_bool_imp(array[int] of var bool: x, array[int] of bool: t, var bool: b);

predicate fzn_table_bool_imp(array[int] of var bool: x, array[int, int] of bool: t, var bool: b) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            jacop_table_bool_imp(x, array1d(t), b)
    );
