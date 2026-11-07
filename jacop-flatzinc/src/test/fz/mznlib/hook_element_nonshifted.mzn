% Element on arrays that do not start at index 1 (array_var_*_element_nonshifted), which JaCoP
% posts with an index offset; the last constraint is not in the root context.
array[3..5] of var 1..4: x;
var 0..7: i;
var 0..5: y;
constraint x[i] = y;
array[-1..2] of int: c = array1d(-1..2, [3, 1, 4, 1]);
var -3..4: j;
var 0..5: z;
constraint c[j] = z;
array[2..4] of var bool: b;
var 1..5: k;
var bool: w;
constraint b[k] = w;
var 1..3: t;
constraint (x[t + 2] = 3) \/ (y = 0);
solve satisfy;
