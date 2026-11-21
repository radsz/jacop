% Cross-checked regression test, written for the global cardinality review (models that rely on global_cardinality).
% Car sequencing (CSPLib 001, the 10-car example): class demand is a closed GCC.
include "globals.mzn";
int: cars = 10; int: classes = 6; int: options = 5;
array[1..classes] of int: demand = [1, 1, 2, 2, 2, 2];
array[1..options] of int: p = [1, 2, 1, 2, 1];
array[1..options] of int: q = [2, 3, 3, 5, 5];
array[1..classes, 1..options] of 0..1: req = [|1,0,1,1,0|0,0,0,1,0|0,1,0,0,1|0,1,0,1,0|1,0,1,0,0|1,1,0,0,0|];
array[1..cars] of var 1..classes: cls;
array[1..options, 1..cars] of var 0..1: has;
constraint global_cardinality_closed(cls, [c | c in 1..classes], demand);
constraint forall(o in 1..options, s in 1..cars)(has[o,s] = req[cls[s], o]);
constraint forall(o in 1..options, s in 1..cars - q[o] + 1)(sum(k in s..s+q[o]-1)(has[o,k]) <= p[o]);
solve satisfy;
output ["cls = \(cls);\n"];
