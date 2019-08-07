predicate jacop_global_cardinality_closed(array[int] of var int: x,
                                          array[int] of int: cover,
                                          array[int] of var int: counts);

predicate fzn_global_cardinality_closed(array[int] of var int: x,
                                    array[int] of int: cover,
                                    array[int] of var int: counts) =
    jacop_global_cardinality_closed(x, cover, counts)
    /\
    % Implied constraint
    length(x) = sum(counts)
    ;
