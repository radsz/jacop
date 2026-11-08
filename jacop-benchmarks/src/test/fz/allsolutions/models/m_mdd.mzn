include "globals.mzn";
% x over 1..3 with x1 < x2 or x1 = x2 = x3; y over 0..2 with y1 = 0 or y2 = 0, and y3 in {0, 2}
% (node 0 is the true terminal)
array[1..3] of var 1..3: x;
array[1..3] of var 0..2: y;
constraint mdd(x, 8, [1, 2, 2, 2, 3, 3, 3, 3],
               12, [1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8],
                   [{1}, {2}, {3}, {1}, 2..3, {2}, {3}, {3}, {1}, 1..3, {2}, {3}],
                   [2, 3, 4, 5, 6, 7, 6, 8, 0, 0, 0, 0]);
constraint mdd(y, 4, [1, 2, 2, 3],
               5, [1, 1, 2, 3, 4], [{0}, 1..2, 0..2, {0}, {0, 2}], [2, 3, 4, 4, 0]);
constraint x[3] >= y[3];
solve satisfy;
