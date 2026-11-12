include "globals.mzn";
array[1..4] of var 1..3: x;
constraint value_precede(1, 3, x);
array[1..4] of var 0..3: y;
constraint value_precede_chain([1, 2, 3], y);
array[1..3] of var 0..3: z;
constraint seq_precede_chain(z);
constraint x[1] != y[1];
solve satisfy;
