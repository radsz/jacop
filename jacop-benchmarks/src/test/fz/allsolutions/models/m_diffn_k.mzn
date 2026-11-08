include "globals.mzn";
% three boxes in 3-d with variable sizes (sizes >= 0, so JaCoP posts DiffnK); 1-d arrays keep
% their names in FlatZinc, so the two flattenings can be compared
array[1..9] of var 0..2: p;
array[1..9] of var 0..2: l;
constraint diffn_k(array2d(1..3, 1..3, p), array2d(1..3, 1..3, l));
constraint forall(i in 0..2)(l[3 * i + 1] + l[3 * i + 2] + l[3 * i + 3] >= 5);
constraint forall(i in 1..9)(p[i] + l[i] <= 3);
constraint p[1] <= p[4] /\ p[4] <= p[7];
solve satisfy;
