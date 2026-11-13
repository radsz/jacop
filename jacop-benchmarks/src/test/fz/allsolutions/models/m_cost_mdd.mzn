include "globals.mzn";
% the first MDD of m_mdd with a cost per arc; the total cost is bounded
array[1..3] of var 1..3: x;
var 0..6: c;
constraint cost_mdd(x, 8, [1, 2, 2, 2, 3, 3, 3, 3],
                    12, [1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 7, 8],
                        [{1}, {2}, {3}, {1}, 2..3, {2}, {3}, {3}, {1}, 1..3, {2}, {3}],
                        [1, 0, 2, 1, 2, 0, 1, 1, 0, 2, 1, 0],
                        [2, 3, 4, 5, 6, 7, 6, 8, 0, 0, 0, 0], c);
constraint c <= 5;
solve satisfy;
