include "globals.mzn";
array[1..4] of var 1..3: x;
constraint all_equal(x[1..3]);
array[1..4] of var 0..3: y;
constraint alldifferent_except_0(y);
array[1..3] of var 0..4: z;
constraint alldifferent_except(z, {0, 2});
constraint y[1] <= x[4] /\ z[1] != y[2];
solve satisfy;
