include "fzn_count_geq.mzn";

% Counted on the 0/1 view of the Booleans by the integer count, so it reaches JaCoP's
% count propagators instead of one reified equality per element.
predicate fzn_count_geq_bool(array[int] of var bool: xs, var bool: value, var int: n) =
  fzn_count_geq([bool2int(x) | x in xs], bool2int(value), n);
