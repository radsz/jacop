include "subcircuit_cost.mzn";
int: n = 5;
array[1..n, 1..n] of int: d = [| 0, 3, 4, 2, 7 | 3, 0, 4, 6, 3 | 4, 4, 0, 5, 8 | 2, 6, 5, 0, 6 | 7, 3, 8, 6, 0 |];
array[1..n] of var 1..n: x;
var 0..60: cost;
constraint subcircuit_cost(x, d, cost);
constraint cost <= 16;
solve satisfy;
