% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Magic sequence: s[i] is the number of occurrences of i in s.
% The counters are the counted variables themselves.
include "globals.mzn";
int: n = 100;
array[0..n-1] of var 0..n-1: s;
constraint global_cardinality(s, array1d(0..n-1, [i | i in 0..n-1]), s);
constraint sum(s) = n;
solve satisfy;
output ["s = \(s);\n"];
