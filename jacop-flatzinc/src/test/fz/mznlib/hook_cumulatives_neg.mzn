include "globals.mzn";
% Upper bounds with a producing task (negative requirement) and a variable bound.
array[1..4] of var 0..3: s;
array[1..4] of var 1..2: m;
var 1..2: b1;
constraint cumulatives(s, [2, 2, 3, 1], [2, 2, -1, 1], m, upper_bound: [b1, 2]);
solve satisfy;
output ["s=\(s) m=\(m) b1=\(b1)\n"];
