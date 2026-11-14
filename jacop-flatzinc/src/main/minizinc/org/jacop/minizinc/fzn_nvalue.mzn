predicate jacop_nvalue(var int: n, array[int] of var int: x);

predicate fzn_nvalue(var int: n, array[int] of var int: x) =
        jacop_nvalue(n, x);
