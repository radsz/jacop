% Cross-checked regression test, from Hakan Kjellerstrand's disjunctive.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written disjunctive replaced by disjunctive on optional tasks and disjunctive_strict.
% Disjunctive scheduling with optional tasks in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 3;
array[1..n] of int: duration = [2, 1, 2];
array[1..n] of var opt 0..3: origin;
array[1..n] of var 0..3: start2;
var 2..n: num_used;

solve satisfy;

constraint
  disjunctive(origin, duration) /\
  num_used = sum(i in 1..n) (bool2int(occurs(origin[i]))) /\
  disjunctive_strict(start2, [1, 2, 1]) /\
  start2[1] <= start2[3]
;

output [
  "origin: ", show(origin), " used: ", show(num_used), " start2: ", show(start2), "\n"
];
