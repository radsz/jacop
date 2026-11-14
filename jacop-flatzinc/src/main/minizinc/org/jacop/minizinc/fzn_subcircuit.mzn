predicate jacop_subcircuit(array[int] of var int: x);

predicate fzn_subcircuit(array[int] of var int: x) = 
  if min(index_set(x)) = 1 then
    jacop_subcircuit(x)
  else
    jacop_subcircuit([x[i] - min(index_set(x)) + 1 | i in index_set(x)])
  endif;
