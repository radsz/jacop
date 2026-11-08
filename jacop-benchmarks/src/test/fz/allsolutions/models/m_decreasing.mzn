include "globals.mzn";
array[1..4] of var 0..4: x;
array[1..4] of var 0..5: y;
constraint decreasing(x);
constraint strictly_decreasing(y);
constraint x[2] <= y[2];
solve satisfy;
