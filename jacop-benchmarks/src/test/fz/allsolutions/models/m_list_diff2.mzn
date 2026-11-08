include "diff2.mzn";
array[1..3] of var 0..3: x;
array[1..3] of var 0..2: y;
array[1..3] of var 1..2: w;
array[1..3] of int: h = [1, 2, 1];
constraint diff2(x, y, w, h);
constraint forall(i in 1..3)(x[i] + w[i] <= 4 /\ y[i] + h[i] <= 3);
solve satisfy;
