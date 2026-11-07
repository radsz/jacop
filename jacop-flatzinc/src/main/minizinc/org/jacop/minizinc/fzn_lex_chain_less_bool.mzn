predicate jacop_lex_chain_less_bool(array[int] of var bool: x, int: vectors);

% the columns of a are the vectors of the chain; array1d(a) lists a row by row
predicate fzn_lex_chain_less_bool(array[int, int] of var bool: a) =
     jacop_lex_chain_less_bool(array1d(a), card(index_set_2of2(a)));
