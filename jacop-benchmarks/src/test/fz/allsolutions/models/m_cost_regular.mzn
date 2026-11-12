include "globals.mzn";
% states 1..3, symbols 1..2; cost of each transition
array[1..6] of var 1..2: x;
var 0..12: c;
constraint cost_regular(x, 3, 2, [| 2, 1 | 3, 1 | 0, 2 |], 1, {1, 2},
                        [| 1, 2 | 0, 3 | 1, 1 |], c);
constraint c <= 8;
solve satisfy;
