include "globals.mzn";
array[1..4] of var 0..3: x;
var 0..12: w;
var 0..30: p;
constraint knapsack([3, 2, 4, 1], [5, 3, 7, 2], x, w, p);
constraint w <= 9 /\ p >= 10;
solve satisfy;
