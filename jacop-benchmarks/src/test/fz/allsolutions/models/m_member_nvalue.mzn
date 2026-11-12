include "globals.mzn";
array[1..4] of var 1..4: x;
var 1..5: y;
var 1..4: n;
constraint member(x, y);
constraint nvalue(n, x);
constraint n <= 3 /\ x[1] <= x[2];
solve satisfy;
