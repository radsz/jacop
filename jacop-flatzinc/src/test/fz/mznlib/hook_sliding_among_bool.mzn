include "globals.mzn";
% Every window of 4 has two or three false values.
array[1..9] of var bool: x;
constraint sliding_among(2, 3, 4, x, false);
solve satisfy;
output ["x=\(x)\n"];
