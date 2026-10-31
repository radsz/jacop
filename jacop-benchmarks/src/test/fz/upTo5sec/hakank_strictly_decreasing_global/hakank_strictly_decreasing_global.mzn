% Cross-checked regression test, from Hakan Kjellerstrand's strictly_decreasing.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written predicates replaced by the strictly_decreasing, strictly_increasing and decreasing globals, with free variables.
% strictly_decreasing, strictly_increasing and decreasing in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
array[1..4] of var 1..6: x;
array[1..3] of var 1..4: y;
array[1..3] of var 1..3: z;
array[1..3] of var bool: b;

solve satisfy;

constraint
  strictly_decreasing(x) /\
  strictly_increasing(y) /\
  decreasing(z) /\
  decreasing(b) /\
  z[2] = 2
;

output [ show(x) ++ " " ++ show(y) ++ " " ++ show(z) ++ " " ++ show(b) ++ "\n" ];
