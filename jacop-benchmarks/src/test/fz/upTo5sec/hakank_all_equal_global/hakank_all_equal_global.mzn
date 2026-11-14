% Cross-checked regression test, from Hakan Kjellerstrand's all_equal_me.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written all_equal replaced by the all_equal global, also reified.
% all_equal in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 4;
array[1..n] of var 0..6: x;
array[1..3] of var 0..2: y;
var bool: y_equal;

solve satisfy;

constraint
  all_equal(x) /\
  (y_equal <-> all_equal(y))
;

output [
  show(x) ++ " " ++ show(y) ++ " " ++ show(y_equal) ++ "\n"
];
