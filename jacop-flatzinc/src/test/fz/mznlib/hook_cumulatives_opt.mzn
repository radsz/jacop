include "globals.mzn";
% Optional tasks on two machines; task i is present iff p[i].
array[1..5] of var 0..4: x;
array[1..5] of var bool: p;
array[1..5] of var 1..2: m;
array[1..5] of var opt 0..4: s = [if p[i] then x[i] else <> endif | i in 1..5];
constraint cumulatives(s, [3, 2, 2, 3, 1], [2, 1, 1, 2, 1], m, upper_bound: [2, 2]);
constraint sum(i in 1..5)(p[i]) >= 4;
constraint forall(i in 1..5)(if p[i] then x[i] + [3, 2, 2, 3, 1][i] <= 6 else x[i] = 0 /\ m[i] = 1 endif);
solve satisfy;
output ["x=\(x) p=\(p) m=\(m)\n"];
