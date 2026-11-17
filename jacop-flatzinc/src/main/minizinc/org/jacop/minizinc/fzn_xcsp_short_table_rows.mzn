% Short table of the XCSP3 bench with its rows one after the other (xcsp_short_table_rows): x
% matches one row of t, where the value star in t matches any value. Posted as a JaCoP
% HybridTable with wildcards on the one-dimensional array itself.
predicate jacop_short_table_int(array[int] of var int: x, array[int] of int: t, int: star);

predicate fzn_xcsp_short_table_rows(array[int] of var int: x, array[int] of int: t, int: star) =
    assert (length(t) mod length(x) == 0,
        "The length of the table must be a multiple of the number of variables",
            jacop_short_table_int(x, t, star)
    );
