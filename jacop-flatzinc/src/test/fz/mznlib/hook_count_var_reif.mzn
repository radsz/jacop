include "globals.mzn";
% count with a variable value under a reification and an implication: decomposed into the literals
% x[i] = y, shared by the counts that compare the same variables (amaze: the neighbour colours).
array[1..4] of var 0..2: x;
var 0..2: v;
var 0..3: c;
var bool: b;
constraint b <-> count(x[1..3], v) = c;
constraint x[4] != 0 -> count(x[1..3], x[4]) = 2;
constraint x[1] != 0 -> count([x[2], x[4]], x[1]) = 1;
solve satisfy;
