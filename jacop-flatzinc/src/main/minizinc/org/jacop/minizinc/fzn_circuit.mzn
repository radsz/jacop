predicate jacop_circuit(array[int] of var int: x);

predicate jacop_circuit_offset(array[int] of var int: x, int: offset);

predicate fzn_circuit(array[int] of var int: x) =
  if min(index_set(x)) = 1 then
    jacop_circuit(x)
  else
    jacop_circuit_offset(x, min(index_set(x)))
  endif;
