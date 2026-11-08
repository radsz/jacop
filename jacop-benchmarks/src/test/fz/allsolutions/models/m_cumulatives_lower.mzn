include "globals.mzn";
int: n = 4;
array[1..n] of var 0..3: s;
array[1..n] of int: d = [2, 1, 2, 2];
array[1..n] of int: r = [1, 2, -1, 1];
array[1..n] of var 1..2: m;
constraint cumulatives(s, d, r, m, [2, 1], true);
constraint forall(i in 1..n)(s[i] + d[i] <= 5);
solve satisfy;
