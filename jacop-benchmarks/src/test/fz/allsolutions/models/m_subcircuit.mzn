include "globals.mzn";
array[1..5] of var 1..5: s;
constraint subcircuit(s);
constraint s[1] != 1 \/ s[2] != 2;
solve satisfy;
