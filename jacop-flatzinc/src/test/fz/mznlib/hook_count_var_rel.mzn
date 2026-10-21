include "globals.mzn";
% count_geq, count_gt, count_leq and count_lt with a variable value and count, posted on
% CountVar (and on Count for a fixed value) without an auxiliary variable in the FlatZinc.
array[1..3] of var 0..2: x;
var 0..2: v;
array[1..4] of var 0..3: n;
constraint count_geq(x, v, n[1]);
constraint count_gt(x, v, n[2]);
constraint count_leq(x, v, n[3]);
constraint count_lt(x, 1, n[4]);
array[1..2] of var bool: bs;
var bool: bvv;
var 0..2: bn;
constraint count_gt(bs, bvv, bn);
solve satisfy;
