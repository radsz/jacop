include "deviation.mzn";
array[1..4] of var 0..4: x;
array[1..3] of var 0..5: y;
var 0..40: d; var 0..100: e;
constraint deviation(x, 8, d);
constraint spread(y, 6, e);
constraint d <= 8 /\ e <= 30;
solve satisfy;
