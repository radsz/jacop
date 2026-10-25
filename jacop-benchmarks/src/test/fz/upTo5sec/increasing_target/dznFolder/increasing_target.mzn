% A long increasing chain with two linear targets (from the ordering audit, b_inc_target):
% one solution or an infeasibility proof after many failures, where most calls of Increasing
% change one variable near one end of the chain.
include "globals.mzn";
int: n; int: d; int: t;
array[1..n] of var 1..d: x;
constraint increasing(x);
constraint sum(x) = (n*(d+1)) div 2;
constraint sum(i in 1..n)(i * x[i]) = t;
solve :: int_search(x, input_order, indomain_min) satisfy;
output ["x = \(x);\n"];
