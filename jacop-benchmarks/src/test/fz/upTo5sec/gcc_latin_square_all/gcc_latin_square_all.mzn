% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% All 4x4 Latin squares (576), each row and column a closed GCC with fixed counts 1.
include "globals.mzn";
int: n = 4;
array[1..n, 1..n] of var 1..n: x;
constraint forall(i in 1..n)(global_cardinality_low_up_closed([x[i,j] | j in 1..n], [k | k in 1..n], [1 | k in 1..n], [1 | k in 1..n]));
constraint forall(j in 1..n)(global_cardinality_closed([x[i,j] | i in 1..n], [k | k in 1..n], [1 | k in 1..n]));
constraint x[1,1] = 1;
solve satisfy;
output ["x = \(x);\n"];
