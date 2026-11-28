include "globals.mzn";
% network_flow_cost with nodes numbered from 0, negative weights and a cost bound.
array[1..5] of var 0..3: flow;
var -10..4: cost;
constraint network_flow_cost([| 0, 1 | 1, 2 | 0, 2 | 2, 1 | 1, 0 |],
                             array1d(0..2, [2, 0, -2]), [-1, 3, 2, -2, 1], flow, cost);
solve satisfy;
output ["flow=\(flow) cost=\(cost)\n"];
