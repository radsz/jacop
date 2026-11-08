include "globals.mzn";
array[1..8] of var 1..3: x;
array[1..7] of var bool: b;
constraint sliding_among(1, 2, 3, x, {1, 2});
constraint sliding_among(1, 2, 4, b, {true});
constraint x[1] = 3 /\ x[4] != 3;
solve satisfy;
