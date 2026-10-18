include "sliding_sum.mzn";

predicate jacop_sequence(array[int] of var int: x, set of int: values, int: q, int: min, int: max);

% Posted as JaCoP's Sequence, which is domain consistent for the whole sequence (it is decomposed
% into a regular constraint over the window contents). The automaton keeps the last
% window_size - 1 memberships, so long windows keep MiniZinc's cumulative-sums decomposition.
predicate fzn_sliding_among_int(int: low, int: up, int: window_size,
                                array[int] of var int: xs, set of int: values) =
  if window_size >= 1 /\ window_size <= 12 /\ window_size <= length(xs) /\ low <= up then
    jacop_sequence(xs, values, window_size, low, up)
  else
    sliding_sum(low, up, window_size, [xi in values | xi in xs])
  endif;
