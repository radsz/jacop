include "among_var.mzn";
array[1..5] of var 0..2: x;
array[1..1] of var 0..2: v;
var 1..3: n;
constraint among_var(n, x, v);
constraint among_var(2, [x[2], x[4], x[5]], [x[1]]);
solve satisfy;
