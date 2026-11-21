predicate jacop_lex_less_int(array[int] of var int: x,
                             array[int] of var int: y);

predicate fzn_lex_less_int(array[int] of var int: x,
                       array[int] of var int: y) =
     jacop_lex_less_int(x, y);


% predicate lex_lt_int(array[int] of var int: x,
%                      array[int] of var int: y) =
%           lex_less(x, y);

