include "globals.mzn";
% Cost regular with negative costs, a cost with holes, a constant and a repeated variable.
var {1, 3}: a;
var 1..3: b;
var {2, 3}: e;
var {-3, -1, 0, 2, 5, 6}: c;
array[1..3, 1..3] of 0..3: d = [| 2, 1, 3 | 3, 0, 1 | 1, 2, 0 |];
array[1..3, 1..3] of int: w = [| 1, -2, 3 | 0, 2, -1 | 4, -3, 2 |];
constraint cost_regular([a, b, 2, e, a, b], 3, 3, d, 1, {1, 3}, w, c);
solve satisfy;
output ["a=\(a) b=\(b) e=\(e) c=\(c)\n"];
