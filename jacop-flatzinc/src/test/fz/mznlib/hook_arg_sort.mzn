% arg_sort with an index set starting at 0, ties and holes: equal values keep the order of their
% indices.
include "globals.mzn";
array[0..4] of var {0, 2, 3}: x;
array[1..5] of var 0..4: p;
constraint x[1] != x[3];
constraint p[2] != 0;
constraint arg_sort(x, p);
solve satisfy;
