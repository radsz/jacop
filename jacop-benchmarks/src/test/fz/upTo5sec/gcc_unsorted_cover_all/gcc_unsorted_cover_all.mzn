% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Closed GCC with an unsorted cover that contains a value no variable can take
% and leaves out a value the variables could take; variable counters, one of
% which is also a counted variable.
include "globals.mzn";
array[1..5] of var {1,3,5,7}: x;
array[1..4] of var 0..5: c;
constraint global_cardinality_closed(x ++ [c[3]], [7, 1, 3, 4], c);
constraint x[1] <= x[5];
solve satisfy;
output ["x = \(x);\nc = \(c);\n"];
