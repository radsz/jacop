include "diff2.mzn";
array[1..3] of var 0..3: x;
array[1..3] of var 0..2: y;
array[1..3] of int: w = [2, 1, 2];
array[1..3] of int: h = [1, 2, 2];
constraint diff2(array2d(1..3, 1..4, [[x[i], y[i], w[i], h[i]][k] | i in 1..3, k in 1..4]));
constraint forall(i in 1..3)(x[i] + w[i] <= 4 /\ y[i] + h[i] <= 3);
solve satisfy;
