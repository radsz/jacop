include "inter_distance.mzn";
array[1..5] of var 0..12: x;
constraint inter_distance(x, 3);
constraint x[1] <= 4 /\ x[2] != 6 /\ x[3] in {1, 2, 7, 8, 9, 12} /\ x[4] >= 5;
solve satisfy;
output ["x = \(x);\n"];
