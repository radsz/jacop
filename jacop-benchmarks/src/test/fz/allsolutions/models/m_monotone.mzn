include "globals.mzn";
array[1..4] of var 1..6: x;
constraint strictly_increasing(x);
array[1..4] of var 1..3: y;
constraint decreasing(y);
array[1..3] of var 1..5: z;
constraint strictly_decreasing(z);
constraint x[2] != y[1] + 2 /\ z[3] <= y[4] + 1;
solve satisfy;
