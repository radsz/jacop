% sort with index sets not starting at 1, holes in the domains and variables in both arrays of
% the second sort.
include "globals.mzn";
array[0..4] of var {0, 1, 3, 4}: x;
array[-1..3] of var 0..4: y;
constraint y[0] != 1;
constraint sort(x, y);
constraint sort([x[2], x[3], y[2]], [x[0], y[1], x[4]]);
solve satisfy;
