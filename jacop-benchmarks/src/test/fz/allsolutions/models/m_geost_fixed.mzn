include "globals.mzn";
int: k = 2;
array[1..3, 1..k] of int: rect_size = [| 2, 1 | 1, 2 | 1, 1 |];
array[1..3, 1..k] of int: rect_offset = [| 0, 0 | 0, 0 | 0, 0 |];
array[1..3] of set of int: shape = [{1}, {2}, {3}];
array[1..3, 1..k] of var 0..2: x;
constraint geost(k, rect_size, rect_offset, shape, x, [1, 2, 3]);
constraint forall(i in 1..3)(x[i, 1] + rect_size[i, 1] <= 3 /\ x[i, 2] + rect_size[i, 2] <= 3);
solve satisfy;
