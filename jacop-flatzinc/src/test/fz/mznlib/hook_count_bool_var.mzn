include "globals.mzn";
% count_* over Booleans with a variable value and a variable count.
array[1..3] of var bool: x;
var bool: v;
array[1..6] of var 0..3: n;
constraint count_eq(x, v, n[1]);
constraint count_neq(x, v, n[2]);
constraint count_lt(x, v, n[3]);
constraint count_leq(x, v, n[4]);
constraint count_gt(x, v, n[5]);
constraint count_geq(x, v, n[6]);
solve satisfy;
output ["x=\(x) v=\(v) n=\(n)\n"];
