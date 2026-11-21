include "globals.mzn";
% Non-deterministic MDD: two edges leave the root with the value 1 and two leave node 3 with 0.
array[1..4] of var 0..2: x;
constraint mdd_nondet(x, 6, [1, 2, 2, 3, 3, 4], 9,
                      [1, 1, 1, 2, 3, 3, 4, 5, 6],
                      [{0, 1}, {1}, {2}, 0..2, {0}, {0, 1}, {2}, {1}, 0..1],
                      [2, 3, 3, 4, 5, 4, 6, 6, 0]);
solve satisfy;
output ["x=\(x)\n"];
