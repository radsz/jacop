include "globals.mzn";
% Cost regular: shifts D, E, N, O (1..4); after a night only a night or a day off.
array[1..4] of var 1..4: x;
var 8..14: c;
array[1..2, 1..4] of 0..2: d = [| 1, 1, 2, 1 | 0, 0, 2, 1 |];
array[1..2, 1..4] of int: w = [| 3, 4, 6, 0 | 3, 4, 5, 0 |];
constraint cost_regular(x, 2, 4, d, 1, 1..2, w, c);
solve satisfy;
output ["x=\(x) c=\(c)\n"];
