include "globals.mzn";
array[1..5] of var 1..4: x;
var 1..4: n;
constraint among(n, x, {1, 3});
constraint x[1] <= x[2];
array[0..4] of var 0..4: s;
constraint circuit(s);
constraint s[0] != x[3] - 1;
solve satisfy;
