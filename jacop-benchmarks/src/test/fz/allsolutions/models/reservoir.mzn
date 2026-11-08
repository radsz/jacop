include "reservoir.mzn";
array[1..5] of var 0..4: t;
array[1..5] of int: c = [2, -1, -1, 1, -1];
constraint reservoir(t, c, 0, 2);
constraint t[1] <= t[2] + 1;
solve satisfy;
