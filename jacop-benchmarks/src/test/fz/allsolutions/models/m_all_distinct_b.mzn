include "all_distinct.mzn";
array[1..5] of var 0..5: x;
constraint all_distinct(x);
constraint x[1] + x[2] = x[3];
solve satisfy;
