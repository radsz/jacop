% Bin packing problem for n items with weights w that are to be packed
% into a minimal number of bins. Each bin has maximum capacity of 100.
%
% Author: Krzysztof Kuchcinski

include "globals.mzn";

int: n;  % number of items
int: c;  % bin capacity
int: m;  % max number of number bins

array[1..n] of int: w;

array[1..n] of var 1..m: b;
var 1..m: max_bin;

constraint
	bin_packing(c, b, w);

constraint
%	max_bin = max(i in 1..m) (b[i]) 
	maximum(max_bin, b)
;

solve :: int_search(b, input_order, indomain_min, complete) minimize max_bin;

output["b = "++show(b), "\nmax_bin = "++show(max_bin)++"\n"];

n = 50;
c = 100;
w = [99, 98, 95, 95, 95, 94, 94, 91, 88, 87, 86, 85, 76, 74, 73, 71, 68, 60, 55, 54, 51, 45, 42, 40, 39, 39, 36, 34, 33, 32, 32, 31, 31, 30, 29, 26, 26, 23, 21, 21, 21, 19, 18, 18, 16, 15, 5, 5, 4, 1];
m = 50;