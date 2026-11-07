include "fzn_lex_chain_lesseq_int.mzn";

predicate fzn_lex_chain_lesseq_orbitope(array[int, int] of var int: a, int: kind) =
     fzn_lex_chain_lesseq_int(a) /\
     if 1 == kind then
       forall (i in index_set_1of2(a)) (1 == sum(row(a, i)))
     elseif 2 == kind then
       forall (i in index_set_1of2(a)) (1 >= sum(row(a, i)))
     else
       true
     endif;
