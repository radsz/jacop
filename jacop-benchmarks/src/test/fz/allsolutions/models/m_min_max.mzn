include "globals.mzn";
array[1..4] of var 0..3: x;
var 0..3: lo;
var 0..3: hi;
constraint lo = min(x);
constraint hi = max(x);
constraint hi - lo >= 2;
constraint x[1] <= x[4];
solve satisfy;
