% Cross-checked regression test, from Hakan Kjellerstrand's cumulative_test.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: cumulative on optional tasks.
% Cumulative with optional tasks in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 4;
array[1..n] of int: duration = [2, 1, 2, 1];
array[1..n] of int: resource = [2, 1, 1, 2];
array[1..n] of var opt 0..2: start;
int: limit = 2;

solve satisfy;

constraint
  cumulative(start, duration, resource, limit) /\
  sum(i in 1..n) (bool2int(occurs(start[i]))) >= 3
;

output [ "start: ", show(start), "\n" ];
