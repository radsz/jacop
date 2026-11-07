include "multi_inter_distance.mzn";
array[1..6] of var 0..7: x;
constraint multi_inter_distance(x, 2, 3);
constraint x[1] <= 2 /\ x[2] != 4 /\ x[3] in {0, 3, 6, 7} /\ x[5] >= 3;
solve satisfy;
output ["x = \(x);\n"];
