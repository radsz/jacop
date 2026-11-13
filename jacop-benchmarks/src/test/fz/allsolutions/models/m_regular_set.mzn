include "globals.mzn";
% regular over the alphabet 2..4 (a set, so jacop_regular_set): words that end in state 3
array[1..4] of var 1..5: x;
constraint regular(x, 3, 2..4, array2d(1..3, 2..4, [2, 1, 0, 2, 3, 1, 0, 3, 1]), 1, {3});
constraint x[1] != x[4];
solve satisfy;
