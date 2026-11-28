% Balancing: minimise the maximum load (bin_packing_load), m bins.
include "globals.mzn";
int: n; int: m; int: c;
array[1..n] of int: w;
array[1..n] of var 1..m: bin;
array[1..m] of var 0..c: load;
var 0..c: maxload;
constraint bin_packing_load(load, bin, w);
constraint forall(j in 1..m)(load[j] <= maxload);
constraint forall(i in 1..min(n, m))(bin[i] <= i);
solve :: int_search(bin, input_order, indomain_min) minimize maxload;
output ["maxload = \(maxload);\n"];
