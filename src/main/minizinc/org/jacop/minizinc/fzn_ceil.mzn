predicate jacop_ceil(var float: p, var int: x);

predicate fzn_ceil(var float: p, var int: x) =
    jacop_ceil(p, x);
