include "globals.mzn";
array[1..5] of var 1..4: x;
array[1..3] of var 0..3: c;
constraint global_cardinality_closed(x, [1, 2, 4], c);
constraint x[1] < x[5];
solve satisfy;
