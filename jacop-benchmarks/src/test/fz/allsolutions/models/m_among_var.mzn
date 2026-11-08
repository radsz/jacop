include "among_var.mzn";
array[1..4] of var 1..3: x;
array[1..2] of var 1..3: v;
var 0..4: n;
var bool: b;
constraint among_var(n, x, v);
constraint v[1] < v[2];
constraint among_var_reif(2, [x[1], x[2], x[3]], [v[1]], b);
solve satisfy;
