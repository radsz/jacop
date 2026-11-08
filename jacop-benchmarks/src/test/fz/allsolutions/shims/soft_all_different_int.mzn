include "nvalue.mzn";
predicate soft_all_different_int(array[int] of var int: x, var int: d, bool: useDec) =
  if useDec then
    d = sum(i, j in index_set(x) where i < j)(bool2int(x[i] = x[j]))
  else
    let { var 0..length(x): nv } in nvalue(nv, x) /\ d = length(x) - nv
  endif;
