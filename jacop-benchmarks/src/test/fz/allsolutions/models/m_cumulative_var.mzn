include "globals.mzn";
array[1..4] of var 0..3: s;
array[1..4] of var 1..2: d;
array[1..4] of var 1..2: r;
var 2..3: cap;
constraint cumulative(s, d, r, cap);
constraint forall(i in 1..4)(s[i] + d[i] <= 4);
constraint d[1] + d[2] >= 3;
solve satisfy;
