include "globals.mzn";
array[1..6] of var 0..4: x;
constraint alldifferent_except_0(x);
constraint sum(x) >= 6;
constraint x[1] <= x[6];
solve satisfy;
