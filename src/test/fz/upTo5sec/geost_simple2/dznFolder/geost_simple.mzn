include "globals.mzn";

int: N = 1; % number rectangles
int: M = 2; % number shapes
int: D = 2; % number dimensions

array[1..N,1..D] of int: size = [| 2, 3
				 |];				      


array[1..N,1..D] of int: offset = [| 0, 0
				   |];

array[1..M] of set of 1..1: shape = [{1}, {1}];

array[1..2,1..D] of var 0..5: x;

array[1..2] of var 1..M: kind = [1, 1];  % used shape

constraint
	geost(D, size, offset, shape, x, kind)
;

solve :: int_search([x[i,j] | i in 1..M, j in 1..D], input_order, indomain_min, complete) satisfy;

output[show(x), show(kind)]