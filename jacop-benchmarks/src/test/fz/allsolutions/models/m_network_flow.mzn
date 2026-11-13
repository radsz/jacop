include "globals.mzn";
% a flow of 3 and a flow of 2 with cost through the same network of 4 nodes and 5 arcs
% (the balances come from a function so that variants keep their sum at zero)
function array[int] of int: balance(int: s) = [s, 0, 0, -s];
array[1..5] of var 0..3: f;
constraint network_flow([|1, 2|1, 3|2, 3|2, 4|3, 4|], balance(3), f);
array[1..5] of var 0..2: g;
var 0..20: c;
constraint network_flow_cost([|1, 2|1, 3|2, 3|2, 4|3, 4|], balance(2), [1, 2, 1, 3, 1], g, c);
constraint c <= 7;
solve satisfy;
