include "globals.mzn";
% network_flow_cost with a self-loop arc, which carries cost but does not change any balance.
array[1..3] of var 0..2: flow;
var 0..8: cost;
constraint network_flow_cost([| 1, 2 | 2, 2 | 2, 3 |], [1, 0, -1], [1, 2, 1], flow, cost);
solve satisfy;
output ["flow=\(flow) cost=\(cost)\n"];
