include "jacop_count_rel.mzn";

% z > n for z = count(xs, value), counted by JaCoP without an auxiliary variable for z.
predicate fzn_count_lt(array[int] of var int: xs, var int: value, var int: n) =
    jacop_count_var_ge(xs, value, n, 1);
