% geost whose kind variables have values outside the index set of shape: kind must take a
% shape index, so the values 0 and 3 are not allowed.
include "globals.mzn";
array[1..2, 1..1] of int: rs = [| 1 | 2 |];
array[1..2, 1..1] of int: ro = [| 0 | 0 |];
array[1..2] of set of 1..2: sh = [{1}, {2}];
array[1..3, 1..1] of var 0..3: x;
array[1..3] of var 0..3: kind;
constraint geost(1, rs, ro, sh, x, kind);
solve satisfy;
