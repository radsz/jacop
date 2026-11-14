include "globals.mzn";
% sum_set on SumWeightedSet: value 2 appears twice, 0 is not among the values and weights can be
% 0. The second constraint has a negative weight and keeps the decomposition.
var set of 0..5: s;
var 0..30: t;
constraint sum_set([1, 2, 3, 2, 7], [3, 0, 4, 1, 5], s, t);
var set of 1..3: s2;
var -5..10: t2;
constraint sum_set([1, 2, 3], [2, -1, 3], s2, t2);
solve satisfy;
