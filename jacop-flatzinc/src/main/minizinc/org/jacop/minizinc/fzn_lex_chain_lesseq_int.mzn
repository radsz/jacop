predicate jacop_lex_chain_lesseq_int(array[int] of var int: x, int: vectors);

% the columns of a are the vectors of the chain; array1d(a) lists a row by row
predicate fzn_lex_chain_lesseq_int(array[int, int] of var int: a) =
     jacop_lex_chain_lesseq_int(array1d(a), card(index_set_2of2(a)));
