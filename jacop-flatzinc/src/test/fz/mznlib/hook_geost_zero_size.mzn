% geost and geost_bb with rectangles of size 0 in some dimension. A rectangle of size 0 still
% overlaps any rectangle it lies strictly inside: two rectangles are apart only when one ends
% at or before the start of the other in some dimension.
include "globals.mzn";
array[1..3, 1..2] of int: rs = [| 0, 1 | 2, 2 | 0, 0 |];
array[1..3, 1..2] of int: ro = [| 0, 0 | 0, 0 | 0, 0 |];
array[1..3] of set of 1..3: sh = [{1}, {2}, {3}];
array[1..3, 1..2] of var 0..1: x;
constraint geost(2, rs, ro, sh, x, [1, 2, 3]);
array[1..2, 1..2] of var 0..2: y;
array[1..2] of var 1..3: ky;
constraint geost_bb(2, rs, ro, sh, y, ky, [1, 0], [3, 2]);
solve satisfy;
