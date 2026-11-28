include "globals.mzn";
% Cost regular whose cost variable is also one of the letters of the word.
array[1..4] of var 1..3: x;
array[1..2, 1..3] of 0..2: d = [| 1, 2, 1 | 2, 1, 0 |];
array[1..2, 1..3] of int: w = [| 0, 1, 2 | 1, 0, 1 |];
constraint cost_regular(x, 2, 3, d, 1, 1..2, w, x[3]);
solve satisfy;
output ["x=\(x)\n"];
