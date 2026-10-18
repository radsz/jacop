include "fzn_count_leq_reif.mzn";

% Counted on the 0/1 view of the Booleans by the integer count, so it reaches JaCoP's
% count propagators instead of one reified equality per element.
predicate fzn_count_leq_bool_reif(array[int] of var bool: xs, var bool: value, var int: n, var bool: b) =
  fzn_count_leq_reif([bool2int(x) | x in xs], bool2int(value), n, b);
