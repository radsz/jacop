% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% All magic sequences of length 4..7, without the redundant sum constraint.
include "globals.mzn";
int: n = 7;
array[0..n-1] of var 0..n-1: s;
constraint global_cardinality_closed(s, array1d(0..n-1, [i | i in 0..n-1]), s);
solve satisfy;
output ["s = \(s);\n"];
