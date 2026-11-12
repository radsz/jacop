include "globals.mzn";
array[1..3, 1..3] of var 1..3: m;
constraint lex_chain_less(m);
array[1..3] of var bool: a;
array[1..3] of var bool: b;
constraint lex_lesseq(a, b);
constraint m[1, 1] = 1 -> a[1];
solve satisfy;
