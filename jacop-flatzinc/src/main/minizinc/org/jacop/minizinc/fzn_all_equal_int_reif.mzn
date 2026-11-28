predicate jacop_all_equal_int_reif(array[int] of var int: x, var bool: b);

predicate fzn_all_equal_int_reif(array[int] of var int: x, var bool: b) =
      jacop_all_equal_int_reif(x, b);
