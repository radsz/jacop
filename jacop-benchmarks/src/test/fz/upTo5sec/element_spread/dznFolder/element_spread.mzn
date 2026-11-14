% Long constant cost tables with spread-out values: y[i] = c[x[i]], with search on the costs.
% Each element has an index of n * 25 or more values, where domain consistency on the value
% (the holes between the table entries) matters.
include "globals.mzn";
int: n; int: m; int: seed;
array[1..m] of int: c = [ ((j * 7919 + seed * 104729) mod 5003) | j in 1..m];
array[1..n] of var 1..m: x;
array[1..n] of var 0..5002: y;
constraint forall(i in 1..n)(y[i] = c[x[i]]);
constraint all_different(x);
constraint forall(i in 1..n)(y[i] mod 7 = i mod 7);
constraint sum(y) mod 13 = 5;
var int: obj = sum(y);
solve :: int_search(y, input_order, indomain_min) minimize obj;
output ["obj = \(obj);\nx = \(x);\n"];
