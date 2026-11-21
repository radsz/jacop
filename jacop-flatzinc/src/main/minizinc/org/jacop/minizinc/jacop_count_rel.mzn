% count(x, y) + k <= c
predicate jacop_count_var_le(array[int] of var int: x, var int: y, var int: c, int: k);

% count(x, y) >= c + k
predicate jacop_count_var_ge(array[int] of var int: x, var int: y, var int: c, int: k);
