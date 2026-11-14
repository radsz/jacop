% Regression test for JaCoP's GCC predicate, written for the global cardinality review.
% Gecode and Chuffed do not know GCC; they were checked with GCC defined as a Count per value.
% Magic sequence with JaCoP's GCC predicate.
include "globals.mzn";
include "GCC.mzn";
int: n = 60;
array[0..n-1] of var 0..n-1: s;
constraint GCC(s, s);
constraint sum(s) = n;
constraint sum(i in 0..n-1)(i * s[i]) = n;
solve satisfy;
output ["s = \(s);\n"];
