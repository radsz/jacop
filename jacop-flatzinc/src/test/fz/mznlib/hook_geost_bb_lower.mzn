% geost_bb with a bounding box that does not start at 0: the box is [l, u) in every dimension,
% so its length is u - l, not u.
include "globals.mzn";
array[1..2, 1..2] of var -1..8: x;
array[1..2] of var 1..2: kind;
constraint geost_bb(2, [| 1, 1 | 2, 1 |], [| 0, 0 | 0, 0 |], [{1}, {2}], x, kind, [2, 1], [5, 3]);
solve satisfy;
