% Short table of the XCSP3 bench (xcsp_short_table): x matches one row of t, where the value
% star in t matches any value. Posted as a JaCoP HybridTable with wildcards.
predicate jacop_short_table_int(array[int] of var int: x, array[int] of int: t, int: star);

predicate fzn_xcsp_short_table(array[int] of var int: x, array[int, int] of int: t, int: star) =
    assert (index_set_2of2(t) == index_set(x),
        "The second dimension of the table must equal the number of variables in the first argument",
            jacop_short_table_int(x, array1d(t), star)
    );
