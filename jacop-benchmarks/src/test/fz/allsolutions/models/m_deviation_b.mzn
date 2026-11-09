include "deviation.mzn";
array[1..3] of var 1..5: x;
array[1..4] of var 0..4: y;
var 0..40: d; var 0..100: e;
constraint deviation(x, 9, d);
constraint spread(y, 8, e);
constraint d <= 6 /\ e <= 12;
solve satisfy;
