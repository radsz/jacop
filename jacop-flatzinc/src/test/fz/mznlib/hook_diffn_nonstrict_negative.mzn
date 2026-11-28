% diffn_nonstrict with sizes that may be negative: MiniZinc's definition allows them, JaCoP's
% Diff2 forces sizes >= 0 and lost those solutions.
include "globals.mzn";
array[1..3] of var 1..2: u;
array[1..3] of var 1..2: v;
array[1..3] of var -1..1: a;
array[1..3] of var 0..1: b;
constraint diffn_nonstrict(u, v, a, b);
constraint forall(i in 1..3)(u[i] + a[i] <= 3);
solve satisfy;
