% Cross-checked regression test, from Hakan Kjellerstrand's alldifferent_except_0_me.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written decomposition replaced by alldifferent_except_0 and alldifferent_except.
% All different except 0 in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 4;
array[1..n] of var 0..n: x;
array[1..4] of var 1..4: y;

solve satisfy;

constraint
  alldifferent_except_0(x) /\
  increasing(x) /\
  alldifferent_except(y, {1, 2}) /\
  y[1] < y[4]
;

output [ show(x) ++ " " ++ show(y) ++ "\n" ];
