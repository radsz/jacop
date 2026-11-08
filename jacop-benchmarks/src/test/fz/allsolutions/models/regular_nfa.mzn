include "globals.mzn";
int: Q = 3;
array[1..Q, 1..2] of set of int: d = [| {1, 2}, {1} | {3}, {} | {}, {3, 1} |];
array[1..6] of var 1..2: x;
constraint regular_nfa(x, Q, 2, d, 1, {1, 3});
solve satisfy;
