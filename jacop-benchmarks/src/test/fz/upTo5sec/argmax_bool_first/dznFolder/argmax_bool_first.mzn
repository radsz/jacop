% First true index of Boolean rows (Boolean arg_max) used as a selector: the first-true indices are
% all different and nearly increasing, every row has three true cells and every column at most w.
include "globals.mzn";
int: n; int: k; int: w;
array[1..k, 1..n] of var bool: b;
array[1..k] of var 1..n: first;
constraint forall(t in 1..k)(first[t] = arg_max(row(b, t)));
constraint forall(t in 1..k-1)(first[t] < first[t+1] + 2);
constraint forall(t in 1..k)(sum(row(b, t)) = 3);
constraint forall(j in 1..n)(sum(col(b, j)) <= w);
constraint all_different(first);
solve :: int_search([bool2int(b[t,j]) | t in 1..k, j in 1..n], input_order, indomain_max) satisfy;
output ["b = \(b);\nfirst = \(first);\n"];
