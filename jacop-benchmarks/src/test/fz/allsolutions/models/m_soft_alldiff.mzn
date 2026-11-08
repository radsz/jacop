include "soft_all_different_int.mzn";
array[1..4] of var 1..3: x;
array[1..4] of var 1..3: y;
var 0..6: d; var 0..4: e;
constraint soft_all_different_int(x, d, true);
constraint soft_all_different_int(y, e, false);
constraint d <= 2 /\ e <= 1;
solve satisfy;
