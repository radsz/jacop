include "globals.mzn";
% Deterministic cost MDD over [x1, x2, x3, x1] (x1 repeated); labels mention 5, outside the
% domains, node 4 has no outgoing edge and costs are negative and positive.
array[1..3] of var 0..2: x;
var -10..10: c;
constraint cost_mdd([x[1], x[2], x[3], x[1]], 7, [1, 2, 2, 3, 3, 4, 4], 9,
               [1, 1, 2, 2, 3, 4, 5, 6, 7],
               [{0}, 1..2, {0, 5}, {2}, {1}, {0}, {1, 2}, {0, 2}, {1}],
               [2, -1, 0, 3, 1, 4, -2, 1, 0],
               [2, 3, 4, 5, 5, 6, 7, 0, 0], c);
constraint c != 1;
solve satisfy;
output ["x=\(x) c=\(c)\n"];
