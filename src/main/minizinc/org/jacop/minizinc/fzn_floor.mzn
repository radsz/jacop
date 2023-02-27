predicate jacop_floor(var float: p, var int: x);

predicate fzn_floor(var float: p, var int: x) =
    jacop_floor(p, x);
