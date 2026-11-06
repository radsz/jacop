% scenario_chance over four scenarios with probabilities 3, 2, 4 and 1 out of 10 that must reach
% 6 out of 10, with negative coefficients, an index set not starting at 1 and a variable twice;
% jacop_expected_sum ties the expectation to z.
include "jacop_prob.mzn";
array[0..3] of var -1..3: x;
var -40..40: z;
constraint x[1] != 1;
constraint scenario_chance([x[0], x[1], x[2], x[3], x[0]],
                           [| 1, 1, 0, 0, 1
                            | 0, 2, -1, 1, 0
                            | -1, 0, 1, 1, 0
                            | 1, 1, 1, 1, 0 |],
                           [3, 2, 1, 4], [3, 2, 4, 1], 10, 6);
constraint jacop_expected_sum(x, [5, -10, 15, 0], 10, z);
solve satisfy;
