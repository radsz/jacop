% Regression test for JaCoP's GCC predicate, written for the global cardinality review.
% Gecode and Chuffed do not know GCC; they were checked with GCC defined as a Count per value.
% JaCoP's own GCC predicate (bounds consistent propagator) on counted variables
% with holes; all solutions.
include "globals.mzn";
include "GCC.mzn";
array[1..5] of var {1,2,4,5}: x;
array[1..5] of var 0..3: c;
constraint GCC(x, c);
constraint c[1] + c[2] = c[4] + c[5] + 1;
constraint x[1] < x[2];
solve satisfy;
output ["x = \(x);\nc = \(c);\n"];
