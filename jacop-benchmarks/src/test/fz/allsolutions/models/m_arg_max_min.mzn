include "globals.mzn";
array[1..4] of var 1..3: x;
var 1..4: i;
var 1..4: j;
constraint i = arg_max(x);
constraint j = arg_min(x);
constraint x[2] != 2;
solve satisfy;
