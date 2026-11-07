include "globals.mzn";
% Lower-bound form keeps the standard decomposition.
array[1..4] of var 0..3: s;
array[1..4] of var 1..2: m;
constraint cumulatives(s, [2, 2, 1, 2], [1, 1, 2, 1], m, lower_bound: [1, 2]);
solve satisfy;
output ["s=\(s) m=\(m)\n"];
