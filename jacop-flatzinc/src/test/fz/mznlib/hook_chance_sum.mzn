% chance_sum over three independent weights with probabilities over 4 that must reach 3 out of 4,
% with an index set not starting at 1, a repeated value in a row (merged), a weight 0 and a
% variable capacity.
include "jacop_prob.mzn";
array[0..2] of var 0..2: x;
var 0..12: c;
constraint chance_sum(x, [| 1, 3 | 2, 2 | 0, 5 |], [| 1, 3 | 2, 2 | 3, 1 |], 4, c, 3);
solve satisfy;
