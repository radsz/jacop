% Cross-checked regression test, from Hakan Kjellerstrand's among_low_up.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written among_low_up and among_diff_0 replaced by the among global, with free variables.
% among with low and up in MiniZinc.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
array[1..4] of var 0..3: x;
var 0..4: nvar;
var 0..4: nzero;
int: low = 1;
int: up = 3;

solve satisfy;

constraint
  nvar = among(x, {0, 2}) /\
  nvar >= low /\
  nvar <= up /\
  % among_diff_0
  nzero = among(x, 1..3) /\
  x[1] <= x[2]
;

output
[
  "x:" ++ show(x) ++ " nvar:" ++ show(nvar) ++ " nzero:" ++ show(nzero) ++ "\n"
];
