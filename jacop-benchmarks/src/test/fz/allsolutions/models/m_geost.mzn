include "globals.mzn";
int: k = 2;
% shapes: 1 = 2x1 bar, 2 = 1x2 bar, 3 = 1x1 square, 4 = L made of two boxes
array[1..5, 1..k] of int: rect_size = [| 2, 1 | 1, 2 | 1, 1 | 2, 1 | 1, 1 |];
array[1..5, 1..k] of int: rect_offset = [| 0, 0 | 0, 0 | 0, 0 | 0, 0 | 0, 1 |];
array[1..4] of set of int: shape = [{1}, {2}, {3}, {4, 5}];
array[1..3, 1..k] of var 0..2: x;
array[1..3] of var 1..4: kind;
constraint geost_bb(k, rect_size, rect_offset, shape, x, kind, [0, 0], [3, 3]);
constraint kind[1] != 3;
solve satisfy;
