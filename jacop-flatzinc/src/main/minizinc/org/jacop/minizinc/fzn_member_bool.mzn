predicate jacop_member_bool(array[int] of var bool: x, var int: y);

predicate fzn_member_bool(array[int] of var bool: x, var bool: y) =
    jacop_member_bool(x, y);
