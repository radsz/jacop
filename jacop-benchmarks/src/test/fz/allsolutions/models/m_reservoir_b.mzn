include "reservoir.mzn";
array[1..5] of var 0..5: t;
array[1..5] of int: c = [1, 1, -2, 2, -1];
constraint reservoir(t, c, 0, 2);
constraint t[2] < t[4];
solve satisfy;
