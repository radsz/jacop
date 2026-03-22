predicate jacop_lex_lesseq_int(array[int] of var int: x,
                             array[int] of var int: y);

predicate fzn_lex_lesseq_int(array[int] of var int: x,
                         array[int] of var int: y) =
     jacop_lex_lesseq_int(x, y);


% predicate lex_leq_int(array[int] of var int: x,
%                       array[int] of var int: y) =
%           lex_lesseq(x, y);

