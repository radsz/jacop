include "globals.mzn";
array[1..5] of var bool: x;
array[1..2] of var bool: y;
array[1..4] of var 0..3: z;
constraint decreasing(x);
constraint strictly_decreasing(y);
constraint strictly_decreasing(z);
solve satisfy;
