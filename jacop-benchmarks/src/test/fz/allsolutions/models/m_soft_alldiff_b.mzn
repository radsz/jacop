include "soft_all_different_int.mzn";
array[1..5] of var 0..2: x;
array[1..3] of var 0..3: y;
var 0..10: d; var 0..3: e;
constraint soft_all_different_int(x, d, true);
constraint soft_all_different_int(y, e, false);
constraint d <= 3;
solve satisfy;
