include "diff2.mzn";
array[1..4] of var 0..3: x;
array[1..4] of var 0..3: y;
array[1..4] of int: w = [1, 2, 1, 2];
array[1..4] of int: h = [2, 1, 1, 2];
constraint diff2(array2d(1..4, 1..4, [[x[i], y[i], w[i], h[i]][k] | i in 1..4, k in 1..4]));
constraint forall(i in 1..4)(x[i] + w[i] <= 3 /\ y[i] + h[i] <= 3);
solve satisfy;
