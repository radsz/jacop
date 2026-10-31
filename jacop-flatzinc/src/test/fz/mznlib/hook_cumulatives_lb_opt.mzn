include "globals.mzn";
% Lower bounds with optional tasks, a negative requirement and a variable duration.
array[1..4] of var 0..3: x;
array[1..4] of var bool: p;
array[1..4] of var 1..2: m;
var 1..2: d4;
array[1..4] of var opt 0..3: s = [if p[i] then x[i] else <> endif | i in 1..4];
constraint cumulatives(s, [2, 2, 1, d4], [1, 2, -1, 2], m, lower_bound: [1, 2]);
constraint forall(i in 1..4)(if p[i] then true else x[i] = 0 /\ m[i] = 1 endif);
solve satisfy;
output ["x=\(x) p=\(p) m=\(m) d4=\(d4)\n"];
