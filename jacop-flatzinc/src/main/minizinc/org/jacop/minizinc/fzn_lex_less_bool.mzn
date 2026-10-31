predicate jacop_lex_less_bool(array[int] of var bool: x,
                             array[int] of var bool: y);

predicate fzn_lex_less_bool(array[int] of var bool: x,
                       array[int] of var bool: y) =
     jacop_lex_less_bool(x, y);



% predicate lex_lt_bool(array[int] of var bool: x,
%                      array[int] of var bool: y) =
%           lex_less(x, y);

