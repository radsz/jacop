% inverse(xs, xs) already makes xs all different; JaCoP posts it as SymmetricAlldifferent
include "fzn_inverse.mzn";
predicate fzn_symmetric_all_different(array[int] of var int: xs) =
    jacop_assignment(xs, xs, min(index_set(xs)), min(index_set(xs)));
