% Table of the XCSP3 bench with its rows one after the other (xcsp_table_rows): posted as the
% JaCoP table of jacop_table_int on the one-dimensional array itself, so that every constraint
% of one table names the same FlatZinc array.
predicate jacop_table_int(array[int] of var int: x, array[int] of int: t);

predicate fzn_xcsp_table_rows(array[int] of var int: x, array[int] of int: t) =
    assert (length(t) mod length(x) == 0,
        "The length of the table must be a multiple of the number of variables",
            jacop_table_int(x, t)
    );
