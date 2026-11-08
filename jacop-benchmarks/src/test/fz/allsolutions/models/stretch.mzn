include "stretch.mzn";
array[1..8] of var 1..3: x;
constraint stretch([1, 2, 3], [2, 1, 2], [3, 2, 3], x);
solve satisfy;
