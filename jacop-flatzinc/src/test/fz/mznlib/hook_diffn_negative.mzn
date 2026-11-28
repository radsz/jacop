% diffn with sizes that may be negative: MiniZinc's definition allows them (a rectangle with
% dx < 0 ends left of x), JaCoP's Diffn forces sizes >= 0 and lost those solutions.
include "globals.mzn";
array[1..3] of var 1..2: x;
array[1..3] of var 1..1: y;
array[1..3] of var -1..2: w;
array[1..3] of var 1..2: h;
constraint diffn(x, y, w, h);
constraint forall(i in 1..3)(x[i] + w[i] < 3);
solve satisfy;
