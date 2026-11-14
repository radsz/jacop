% circuit on arrays numbered from 0 and from -2 (index sets not starting at 1).
include "globals.mzn";
array[0..4] of var 0..5: x;
array[-2..1] of var -3..1: y;
constraint x[0] != 2;
constraint circuit(x);
constraint circuit(y);
solve satisfy;
