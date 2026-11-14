include "globals.mzn";
array[1..3] of var 0..3: x;
array[1..3] of var 0..2: y;
array[1..3] of var 0..2: w;
array[1..3] of var 1..2: h;
constraint diffn(x, y, w, h);
constraint forall(i in 1..3)(x[i] + w[i] <= 4 /\ y[i] + h[i] <= 3);
constraint w[1] + w[2] + w[3] >= 4 /\ x[1] <= x[2];
solve satisfy;
