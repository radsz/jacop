% Cross-checked regression test, from Hakan Kjellerstrand's nvalues.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: all_different with the domain annotation and nvalue.
% Permutations with the domain consistent alldifferent in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 5;
array[1..n] of var 1..n: x;
var 1..n: nv;
array[1..n] of var 1..3: y;

solve satisfy;

constraint
  all_different(x) :: domain /\
  x[1] < x[2] /\ x[3] < x[4] /\ x[2] < x[4] /\
  nv = nvalue(y) /\ nv = 2 /\ y[1] = 1
;

output [ show(x), " ", show(y), " ", show(nv), "\n" ];
