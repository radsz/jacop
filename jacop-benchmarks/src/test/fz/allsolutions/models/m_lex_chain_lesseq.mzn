include "globals.mzn";
% the columns of a 2 x 3 int matrix are lexicographically non-decreasing
array[1..2, 1..3] of var 0..2: a;
constraint lex_chain_lesseq(a);
constraint a[1, 1] + a[2, 3] <= 3;
solve satisfy;
