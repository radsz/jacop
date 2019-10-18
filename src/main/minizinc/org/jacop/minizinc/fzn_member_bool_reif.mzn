predicate jacop_member_bool_reif(array[int] of var bool: x, var int: y, var bool: b);

predicate fzn_member_bool_reif(array[int] of var bool: x, var bool: y, var bool: b) =
    jacop_member_bool_reif(x, y, b);
