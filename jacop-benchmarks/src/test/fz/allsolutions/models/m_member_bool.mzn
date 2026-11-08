include "globals.mzn";
array[1..4] of var bool: x;
var bool: y; var bool: z; var bool: b;
constraint member(x, y);
constraint b <-> member([x[1], x[2]], z);
constraint sum(i in 1..4)(bool2int(x[i])) = 2;
solve satisfy;
