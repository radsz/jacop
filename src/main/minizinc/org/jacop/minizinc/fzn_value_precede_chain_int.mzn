predicate jacop_value_precede_chain_int(array[int] of int: T, array[int] of var int: X);

predicate fzn_value_precede_chain_int(array[int] of int: T, array[int] of var int: X) =
    jacop_value_precede_chain_int(T, X);
