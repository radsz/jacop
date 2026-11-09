include "globals.mzn";
array[1..5] of var bool: x;
var bool: y; var bool: b1; var bool: b2;
constraint member([x[1], x[3], x[5]], y);
constraint b1 <-> member([x[2], x[4]], true);
constraint b2 <-> member(x, false);
solve satisfy;
