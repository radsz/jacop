include "all_distinct.mzn";
int: n = 4; int: m = 6;
array[1..n] of var 1..m: x;
constraint all_distinct(x);
constraint sum(x) <= 3 * n;
solve satisfy;
