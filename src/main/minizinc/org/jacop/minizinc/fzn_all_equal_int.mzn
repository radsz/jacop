predicate jacop_all_equal_int(array[int] of var int: x);

predicate fzn_all_equal_int(array[int] of var int: x) =
      jacop_all_equal_int(x);
