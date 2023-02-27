predicate jacop_round(var float: p, var int: x);

predicate fzn_round(var float: p, var int: x) =
    jacop_round(p, x);
