include "sliding_sum.mzn";

predicate jacop_sequence(array[int] of var int: x, set of int: values, int: q, int: min, int: max);

% Posted as JaCoP's Sequence, which is domain consistent for the whole sequence. Its propagator
% works on the cumulative sums of the memberships, so its cost does not grow as 2^window_size,
% but it is linear in the length of xs per call. On left-to-right search MiniZinc's
% cumulative-sums decomposition gives the same tree at a lower cost per node, and from windows
% of about 14 that outweighs the smaller trees of other search orders, so longer windows keep
% the decomposition.
predicate fzn_sliding_among_int(int: low, int: up, int: window_size,
                                array[int] of var int: xs, set of int: values) =
  if window_size >= 1 /\ window_size <= 12 then
    jacop_sequence(xs, values, window_size, low, up)
  else
    sliding_sum(low, up, window_size, [xi in values | xi in xs])
  endif;
