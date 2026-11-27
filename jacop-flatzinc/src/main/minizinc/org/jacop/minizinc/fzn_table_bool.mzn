predicate jacop_table_bool(array[int] of var bool: x, array[int] of bool: t);

predicate fzn_table_bool(array[int] of var bool: x, array[int, int] of bool: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            % no variable: array1d(t) is empty whatever the number of rows of t
            if length(x) = 0 then card(index_set_1of2(t)) > 0 else jacop_table_bool(x, array1d(t)) endif
    );
