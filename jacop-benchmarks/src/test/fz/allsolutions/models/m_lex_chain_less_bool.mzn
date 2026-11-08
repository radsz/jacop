include "globals.mzn";
array[1..3,1..3] of var bool: a;
array[1..3,1..2] of var bool: c;
constraint lex_chain_less(a);
constraint lex_chain_lesseq(c);
constraint sum(i, j in 1..3)(bool2int(a[i, j])) <= 4;
solve satisfy;
