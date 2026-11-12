include "globals.mzn";
array[1..5] of var 1..3: x;
constraint count(x, 3) >= 2;
constraint count(x, 1) <= 2;
constraint x[1] <= x[2];
solve satisfy;
