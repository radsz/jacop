% Cross-checked regression test, from Hakan Kjellerstrand's diffn_me.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% Variant: the hand-written diffn replaced by diffn_nonstrict, with zero-width rectangles.
% diffn in MiniZinc: placing rectangles, zero-sized ones allowed to overlap.
%
% This MiniZinc model was created by Hakan Kjellerstrand, hakank@gmail.com
% See also my MiniZinc page: http://www.hakank.org/minizinc
%
include "globals.mzn";
int: n = 3;
array[1..n] of var 0..2: x;
array[1..n] of var 0..1: y;
array[1..n] of var 0..2: w;
array[1..n] of int: h = [1, 2, 1];

solve satisfy;

constraint
  diffn_nonstrict(x, y, w, h) /\
  forall(i in 1..n) (x[i] + w[i] <= 3) /\
  y[2] = 0 /\
  sum(w) >= 4
;

output [ "x: ", show(x), " y: ", show(y), " w: ", show(w), "\n" ];
