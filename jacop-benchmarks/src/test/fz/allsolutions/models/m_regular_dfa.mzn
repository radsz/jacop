include "globals.mzn";
array[1..6] of var 1..3: x;
% no two equal adjacent values of 3, a 1 is followed by a 2 or 3
constraint regular(x, 4, 3, [| 2, 3, 4 | 0, 3, 4 | 2, 3, 4 | 2, 3, 0 |], 1, {1, 2, 3, 4});
constraint x[1] + x[6] >= 3;
solve satisfy;
