predicate jacop_member_int_reif(array[int] of var int: x, var int: y, var bool: b);

predicate fzn_member_int_reif(array[int] of var int: x, var int: y, var bool: b) =
    jacop_member_int_reif(x, y, b);
