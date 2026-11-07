% Cross-checked regression test, from Hakan Kjellerstrand's lex2_me.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the matrix made Boolean and free, lex_less on rows and lex_lesseq on columns.
% lex2 in MiniZinc, on a Boolean matrix.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: r = 3;
int: c = 3;
array[1..r, 1..c] of var bool: x;

solve satisfy;

constraint
  forall(i in 2..r) (
     lex_less([x[i-1, j] | j in 1..c], [x[i, j] | j in 1..c])
  )
  /\
  forall(j in 2..c) (
     lex_lesseq([x[i, j-1] | i in 1..r], [x[i, j] | i in 1..r])
  )
;

output [
 if j = 1 then "\n" else " " endif ++ show(x[i,j]) | i in 1..r, j in 1..c
] ++ ["\n"];
