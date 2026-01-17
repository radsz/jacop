predicate jacop_link_set_to_booleans(var set of int: s, array[int] of var bool: b, int: offset);

predicate fzn_link_set_to_booleans(var set of int: s, array[int] of var bool: b) =
  if min(index_set(b)) < 0 then
    forall(i in index_set(b)) ( b[i] <-> i in s )
  else
    jacop_link_set_to_booleans(s,b,min(index_set(b)))
  endif
  ;
