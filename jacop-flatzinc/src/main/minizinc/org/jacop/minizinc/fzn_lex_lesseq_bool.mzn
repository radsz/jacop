predicate jacop_lex_lesseq_bool(array[int] of var bool: x,
                             array[int] of var bool: y);

predicate fzn_lex_lesseq_bool(array[int] of var bool: x,
                         array[int] of var bool: y) =
     jacop_lex_lesseq_bool(x, y);

% predicate lex_leq_bool(array[int] of var bool: x,
%                        array[int] of var bool: y) =
%           lex_lesseq(x, y);

