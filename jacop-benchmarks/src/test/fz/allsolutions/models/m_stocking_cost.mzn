include "stocking_cost.mzn";
array[1..4] of var 1..5: x;
var 0..30: cost;
constraint stocking_cost(x, [3, 4, 5, 5], [1, 2, 1, 3], cost, 2);
constraint cost <= 6;
solve satisfy;
