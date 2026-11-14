include "globals.mzn";
% Reified regular: b holds exactly when x is accepted (strings over 1..2 with no two 2s in a row).
array[1..4] of var 1..2: x;
var bool: b;
array[1..3, 1..2] of 0..3: d = [| 2, 3 | 2, 3 | 2, 0 |];
constraint b <-> regular(x, 3, 2, d, 1, 1..3);
solve satisfy;
output ["x=\(x) b=\(b)\n"];
