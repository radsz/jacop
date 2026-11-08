include "globals.mzn";
array[1..4] of var 0..3: x;
array[1..4] of var 0..3: y;
array[1..4] of var 1..4: p;
constraint sort(x, y);
constraint p = arg_sort(x);
constraint x[1] != x[2];
solve satisfy;
