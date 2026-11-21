% chance_table over six scenarios of four shared tables, with an index set not starting at 1, a
% repeated tuple, a tuple outside the domains, an empty table, a scenario of no table (it always
% holds) and a scenario of weight 0; the weight of the scenarios that hold must reach 6.
include "jacop_prob.mzn";
array[0..2] of var 0..2: x;
var 0..12: p;
constraint chance_table(x, [1, 2, 2, 1], [1, 2, 3, 1, 3, 2],
                        [2, 4, 3, 0], [0, 1, 0, 1, 1, 2, 2, 2, 2, 2, 2, 0, 1, 1, 0, 5],
                        [2, 1, 1, 0, 1, 2], [1, 2, 3, 2, 4, 1, 3], [3, 2, 4, 1, 2, 0], p);
constraint p >= 6;
solve satisfy;
