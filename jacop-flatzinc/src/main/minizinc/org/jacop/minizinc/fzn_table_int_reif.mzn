predicate jacop_table_int_reif(array[int] of var int: x, array[int] of int: t, var bool: b);

predicate fzn_table_int_reif(array[int] of var int: x, array[int, int] of int: t, var bool: b) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            % no variable: array1d(t) is empty whatever the number of rows of t
            if length(x) = 0 then b <-> card(index_set_1of2(t)) > 0 else jacop_table_int_reif(x, array1d(t), b) endif
    );

predicate jacop_table_int_imp(array[int] of var int: x, array[int] of int: t, var bool: b);

predicate fzn_table_int_imp(array[int] of var int: x, array[int, int] of int: t, var bool: b) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            % no variable: array1d(t) is empty whatever the number of rows of t
            if length(x) = 0 then b -> card(index_set_1of2(t)) > 0 else jacop_table_int_imp(x, array1d(t), b) endif
    );
