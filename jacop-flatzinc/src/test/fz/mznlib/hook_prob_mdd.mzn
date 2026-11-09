% prob_mdd over x[0], a chance level of probabilities over 4 and x[1], with an index set not
% starting at 1, a missing decision edge, a chance node of mass below 1, and a scale of 16; the
% scaled probability must reach 4.
include "jacop_prob.mzn";
array[0..1] of var 0..2: x;
var 0..16: p;
constraint prob_mdd(x, [1, 0, 2], [1, 4, 1], [1, 2, 2], [2, 2, 1, 2, 1],
                    [0, 2, 3, 1, 2, 0, 1, 2], [1, 2, 1, 2, 1, 0, 0, 0], 16, p);
constraint p >= 4;
solve satisfy;
