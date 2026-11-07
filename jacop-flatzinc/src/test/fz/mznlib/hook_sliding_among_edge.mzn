include "globals.mzn";
% Edge cases: a window covering the whole array, values covering the whole domain,
% values outside the domain and a window over the size limit (decomposition kept).
array[1..5] of var 1..3: x;
array[1..13] of var bool: y;
constraint sliding_among(2, 3, 5, x, {1});
constraint sliding_among(0, 5, 2, x, {1, 2, 3});
constraint sliding_among(0, 1, 2, x, {3, 7});
constraint sliding_among(6, 6, 13, y, true) /\ sum(y[1..4]) = 4;
solve satisfy;
output ["x=\(x) y=\(y)\n"];
