include "cumulative.mzn";
include "disjunctive.mzn";
% equal lengths and resource uses: multi_inter_distance on s, inter_distance on t
array[1..6] of var 0..7: s;
array[1..4] of var 0..9: t;
constraint cumulative(s, [3 | i in 1..6], [2 | i in 1..6], 5);
constraint disjunctive(t, [3 | i in 1..4]);
constraint s[1] <= 2 /\ s[2] != 4 /\ s[3] in {0, 3, 6, 7} /\ t[1] != 3 /\ t[2] in {0, 4, 5, 9};
solve satisfy;
output ["s = \(s);\nt = \(t);\n"];
