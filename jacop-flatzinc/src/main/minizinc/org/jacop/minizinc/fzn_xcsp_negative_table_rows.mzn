% Negative table of the XCSP3 bench with its rows one after the other
% (xcsp_negative_table_rows): x matches no row of t. Posted as a JaCoP NegativeTable on the
% one-dimensional array itself.
predicate jacop_negative_table_int(array[int] of var int: x, array[int] of int: t);

predicate fzn_xcsp_negative_table_rows(array[int] of var int: x, array[int] of int: t) =
    assert (length(t) mod length(x) == 0,
        "The length of the table must be a multiple of the number of variables",
            jacop_negative_table_int(x, t)
    );
