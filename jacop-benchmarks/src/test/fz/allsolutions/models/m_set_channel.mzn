include "globals.mzn";
array[1..4] of var 1..3: x;
array[1..3] of var set of 1..4: y;
constraint int_set_channel(x, y);
array[1..3] of var set of 1..3: z;
constraint all_disjoint(z);
constraint forall(i in 1..3)(card(z[i]) >= 1);
constraint x[1] in z[1];
solve satisfy;
