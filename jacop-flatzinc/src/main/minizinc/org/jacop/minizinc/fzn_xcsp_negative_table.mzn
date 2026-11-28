% Negative table of the XCSP3 bench (xcsp_negative_table): x matches no row of t. Posted as a
% JaCoP NegativeTable.
predicate jacop_negative_table_int(array[int] of var int: x, array[int] of int: t);

predicate fzn_xcsp_negative_table(array[int] of var int: x, array[int, int] of int: t) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            jacop_negative_table_int(x, array1d(t))
    );
