include "globals.mzn";
int: n = 4;
array[1..n] of var opt 0..3: s;
array[1..n] of int: d = [2, 1, 2, 2];
array[1..n] of int: r = [1, 2, 1, 1];
array[1..n] of var 1..2: m;
% lower bounds: every machine in use has at least the bound in use
constraint cumulatives(s, d, r, m, [1, 1], false);
constraint forall(i in 1..n)(occurs(s[i]) -> deopt(s[i]) + d[i] <= 5);
constraint sum(i in 1..n)(bool2int(occurs(s[i]))) >= 2;
solve satisfy;
