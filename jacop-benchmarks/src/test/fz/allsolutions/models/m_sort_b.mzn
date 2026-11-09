include "globals.mzn";
array[1..5] of var 1..3: x;
array[1..5] of var 1..3: y;
array[1..5] of var 1..5: p;
constraint sort(x, y);
constraint p = arg_sort(x);
constraint y[3] = 2;
solve satisfy;
