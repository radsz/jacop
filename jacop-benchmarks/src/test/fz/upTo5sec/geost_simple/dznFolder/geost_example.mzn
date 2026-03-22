include "globals.mzn";

int: N = 7; % number rectangles
int: M = 4; % number shapes
int: L = 3; % number of kinds
int: D = 2; % number dimensions

array[1..N,1..D] of int: size = [| 2, 1
		    	 	 | 1, 2
				 | 3, 1

				 | 2, 1
				 | 2, 1
				 | 1, 1

				 | 2, 3

				 |];				      


array[1..N,1..D] of int: offset = [| 0, 0
		    	 	   | 0, 1
				   | 1, 2

				   | 0, 0
				   | 0, 2
				   | 1, 1

				   | 0, 0

				   |];

array[1..M] of set of int: shape = [1..3, 4..6, {7}, {7}];

array[1..L,1..D] of var 0..5: x;

array[1..L] of var 1..M: kind; % = [1, 2, 3];  % used shape

array[1..D] of int: l = [0,0];
array[1..D] of int: u = [5,5];


constraint
	geost_bb(D, size, offset, shape, x, kind, l, u)
;

solve :: int_search([x[i,j] | i in 1..L, j in 1..D], input_order, indomain_min, complete) satisfy;

output[show(x), show(kind)]