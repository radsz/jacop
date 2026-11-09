include "inter_distance.mzn";
include "multi_inter_distance.mzn";
array[1..4] of var 0..7: x;
array[1..5] of var 0..4: y;
constraint inter_distance(x, 2);
constraint multi_inter_distance(y, 2, 2);
constraint x[1] < x[2] /\ x[2] < x[3];
solve satisfy;
