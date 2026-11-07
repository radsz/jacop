% Cross-checked regression test, from Hakan Kjellerstrand's argmax.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written argmax/argmin predicates replaced by arg_max and arg_min, also on Booleans.
% Argmax and argmin in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 5;
array[1..n] of var 1..n: x;
var lb_array(x)..ub_array(x): pos;
array[1..3] of var bool: b;
var 1..3: bmax;
var 1..3: bmin;

solve satisfy;

constraint
  alldifferent(x) /\
  pos = arg_max(x) /\
  arg_min(x) = 2 /\
  bmax = arg_max(b) /\
  bmin = arg_min(b)
;

output
[
  "x: " ++ show(x) ++ "\n" ++
  "pos: " ++ show(pos) ++ "\n" ++
  "b: " ++ show(b) ++ " " ++ show(bmax) ++ " " ++ show(bmin) ++ "\n"
];
