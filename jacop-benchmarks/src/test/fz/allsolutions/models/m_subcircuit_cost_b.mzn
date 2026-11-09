include "subcircuit_cost.mzn";
int: n = 4;
array[1..n, 1..n] of int: d = [| 0, 1, 5, 2 | 4, 0, 1, 3 | 2, 6, 0, 1 | 1, 2, 3, 0 |];
array[1..n] of var 1..n: x;
var 0..40: cost;
constraint subcircuit_cost(x, d, cost);
constraint x[1] != 1;
solve satisfy;
