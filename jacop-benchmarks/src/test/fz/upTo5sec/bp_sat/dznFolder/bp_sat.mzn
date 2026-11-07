% Bin packing feasibility: n items (sorted by decreasing weight), m bins of capacity c.
% Fixed search: items in input order, smallest bin first; first bin of item i <= i (symmetry).
include "globals.mzn";
int: n; int: m; int: c;
array[1..n] of int: w;
array[1..n] of var 1..m: bin;
constraint bin_packing(c, bin, w);
constraint forall(i in 1..min(n, m))(bin[i] <= i);
solve :: int_search(bin, input_order, indomain_min) satisfy;
output ["bin = \(bin);\n"];
