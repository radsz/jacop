include "jacop_count_rel.mzn";

% z <= n for z = count(xs, value), counted by JaCoP without an auxiliary variable for z.
predicate fzn_count_geq(array[int] of var int: xs, var int: value, var int: n) =
    jacop_count_var_le(xs, value, n, 0);
