include "stretch.mzn";
array[1..9] of var 0..2: x;
constraint stretch([0, 1, 2], [1, 2, 1], [2, 3, 4], x);
constraint x[1] != x[9];
solve satisfy;
