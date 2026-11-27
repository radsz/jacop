predicate jacop_table_int(array[int] of var int: x, array[int] of int: t);

predicate fzn_table_int(array[int] of var int: x, array[int, int] of int: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            % no variable: array1d(t) is empty whatever the number of rows of t
            if length(x) = 0 then card(index_set_1of2(t)) > 0 else jacop_table_int(x, array1d(t)) endif
    );
