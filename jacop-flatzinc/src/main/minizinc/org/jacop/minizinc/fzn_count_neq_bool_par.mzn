include "fzn_count_neq_par.mzn";

% Counted on the 0/1 view of the Booleans by the integer count, so it reaches JaCoP's
% count propagators instead of one reified equality per element.
predicate fzn_count_neq_bool_par(array[int] of var bool: xs, bool: value, int: n) =
  fzn_count_neq_par([bool2int(x) | x in xs], bool2int(value), n);
