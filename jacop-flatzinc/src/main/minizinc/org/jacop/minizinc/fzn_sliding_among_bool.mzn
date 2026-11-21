include "fzn_sliding_among_int.mzn";

predicate fzn_sliding_among_bool(int: low, int: up, int: window_size,
                                 array[int] of var bool: xs, bool: value) =
  if window_size >= 1 then
    jacop_sequence([bool2int(xi) | xi in xs], {bool2int(value)}, window_size, low, up)
  else
    sliding_sum(low, up, window_size, [xi = value | xi in xs])
  endif;
