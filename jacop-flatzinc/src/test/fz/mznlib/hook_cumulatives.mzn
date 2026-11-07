include "globals.mzn";
% Two machines, variable machine assignment, one variable duration and a variable bound.
array[1..5] of var 0..5: s;
array[1..5] of var 1..2: m;
var 1..2: d5;
var 2..3: b2;
constraint cumulatives(s, [3, 2, 2, 3, d5], [1, 2, 1, 2, 1], m, upper_bound: [2, b2]);
constraint s[1] + 3 <= 7 /\ s[2] + 2 <= 7 /\ s[3] + 2 <= 7 /\ s[4] + 3 <= 7 /\ s[5] + d5 <= 7;
solve satisfy;
output ["s=\(s) m=\(m) d5=\(d5) b2=\(b2)\n"];
