predicate jacop_seq_precede_chain_int(array[int] of var int: x);

predicate fzn_seq_precede_chain_int(array[int] of var int: X) =
  if length(X) = 0 then
    true
  else
    jacop_seq_precede_chain_int(X)
  endif;
