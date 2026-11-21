include "globals.mzn";
% Every window of 3 has one or two values from {1, 3}; x[4] cannot take a value from the set.
array[1..8] of var 1..4: x;
constraint x[4] in {2, 4};
constraint sliding_among(1, 2, 3, x, {1, 3});
solve satisfy;
output ["x=\(x)\n"];
