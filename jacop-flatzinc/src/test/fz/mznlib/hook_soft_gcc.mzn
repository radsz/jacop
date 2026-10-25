% soft_global_cardinality_int with both violation measures: unsorted values, a variable whose
% domain has values that are not counted, and soft counters that sum to less than length(x).
include "jacop.mzn";
array[1..4] of var 0..3: x;
array[1..2] of var 0..4: hard;
array[1..2] of var {0, 2, 3}: soft;
array[1..2] of var 0..8: cost;
constraint soft_global_cardinality_int(x, [2, 1], hard, soft, cost[1], false);
constraint soft_global_cardinality_int(x, [2, 1], hard, soft, cost[2], true);
constraint cost[2] >= 1 /\ x[1] != 3;
solve satisfy;
