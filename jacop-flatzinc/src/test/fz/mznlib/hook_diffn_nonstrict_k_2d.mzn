% diffn_nonstrict_k in 2 dimensions is posted as the native non-strict diffn.
include "globals.mzn";
array[1..3, 1..2] of var 0..2: p;
array[1..3, 1..2] of var 0..2: s;
constraint forall(i in 1..3, j in 1..2)(p[i, j] + s[i, j] <= 2);
constraint s[1, 1] = 2 /\ s[2, 2] = 1 /\ s[3, 1] = s[3, 2];
constraint diffn_nonstrict_k(p, s);
solve satisfy;
