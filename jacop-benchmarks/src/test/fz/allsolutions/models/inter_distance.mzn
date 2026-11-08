include "inter_distance.mzn";
include "multi_inter_distance.mzn";
array[1..3] of var 0..7: x;
array[1..4] of var 0..4: y;
constraint inter_distance(x, 3);
constraint multi_inter_distance(y, 2, 2);
constraint x[1] < x[2] /\ y[1] <= y[2];
solve satisfy;
