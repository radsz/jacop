% geost with rectangles numbered from 0 and shapes numbered from 5 (index sets not starting at 1).
include "globals.mzn";
array[0..2, 1..2] of int: rs = array2d(0..2, 1..2, [1, 1,  2, 1,  1, 2]);
array[0..2, 1..2] of int: ro = array2d(0..2, 1..2, [0, 0,  0, 0,  1, 0]);
array[5..6] of set of 0..2: sh = array1d(5..6, [{0}, {1, 2}]);
array[1..2, 1..2] of var 0..2: x;
array[1..2] of var 5..6: kind;
constraint geost(2, rs, ro, sh, x, kind);
solve satisfy;
