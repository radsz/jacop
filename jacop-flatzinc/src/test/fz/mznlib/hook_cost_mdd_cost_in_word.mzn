include "globals.mzn";
% Cost MDD whose total cost is also the last variable of the word.
array[1..3] of var 0..3: x;
constraint cost_mdd([x[1], x[2], x[3]], 5, [1, 2, 2, 3, 3], 8,
               [1, 1, 2, 2, 3, 4, 4, 5],
               [{0}, {1, 2}, {0, 1}, {2}, 0..3, {1}, {2, 3}, {0}],
               [1, 0, 2, 1, 0, 1, -1, 0],
               [2, 3, 4, 5, 5, 0, 0, 0], x[3]);
solve satisfy;
output ["x=\(x)\n"];
