include "globals.mzn";
array[1..5] of var 1..4: x;
constraint global_cardinality_closed(x, [1, 2, 4], [0, 1, 1], [2, 3, 2]);
constraint x[1] <= x[2];
solve satisfy;
