include "stocking_cost.mzn";
array[1..5] of var 1..6: x;
var 0..40: cost;
constraint stocking_cost(x, [2, 3, 4, 6, 6], [2, 1, 1, 1, 2], cost, 1);
constraint cost <= 5;
solve satisfy;
