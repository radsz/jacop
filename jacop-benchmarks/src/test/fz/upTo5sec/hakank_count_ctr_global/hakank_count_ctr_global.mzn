% Cross-checked regression test, from Hakan Kjellerstrand's count_ctr.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written count_ctr replaced by count with a variable value, count reifications and global_cardinality_low_up_closed.
% count_ctr in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 4;
array[1..n] of var 1..3: x;
var 0..n: nvar;
var 1..3: val;
var bool: two_threes;
var bool: few_ones;

solve satisfy;

constraint
  nvar = count(x, val) /\
  nvar >= 2 /\
  count(x, 2) <= 2 /\
  count(x, 1) >= 1 /\
  (two_threes <-> count(x, 3) = 2) /\
  (few_ones <-> count(x, 1) <= 1) /\
  global_cardinality_low_up_closed(x, [1, 2, 3], [1, 0, 0], [3, 2, 3])
;

output [
 "x: " ++ show(x) ++ " nvar: " ++ show(nvar) ++ " val: " ++ show(val) ++ " " ++
 show(two_threes) ++ " " ++ show(few_ones) ++ "\n"
];
