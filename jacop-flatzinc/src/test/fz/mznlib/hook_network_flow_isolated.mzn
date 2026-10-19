include "globals.mzn";
% network_flow where node 1 has no arcs: the arcs start at node 2, but balances are indexed by node.
array[1..3] of var 0..3: flow;
constraint network_flow([| 2, 3 | 3, 4 | 2, 4 |], [0, 2, 0, -2], flow);
solve satisfy;
output ["flow=\(flow)\n"];
