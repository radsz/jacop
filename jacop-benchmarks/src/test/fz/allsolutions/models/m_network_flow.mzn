include "globals.mzn";
% a flow of 3 and a flow of 2 with cost through the same network of 4 nodes and 5 arcs
array[1..5] of var 0..3: f;
constraint network_flow([|1, 2|1, 3|2, 3|2, 4|3, 4|], [3, 0, 0, -3], f);
array[1..5] of var 0..2: g;
var 0..20: c;
constraint network_flow_cost([|1, 2|1, 3|2, 3|2, 4|3, 4|], [2, 0, 0, -2], [1, 2, 1, 3, 1], g, c);
constraint c <= 7;
solve satisfy;
