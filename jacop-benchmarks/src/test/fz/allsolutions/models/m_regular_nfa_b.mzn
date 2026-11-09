include "globals.mzn";
% NFA over {1,2,3}: words where a 3 is followed by two symbols, nondeterministically guessed
int: Q = 4;
array[1..Q, 1..3] of set of int: d = [| {1}, {1}, {1, 2} | {3}, {3}, {3} | {4}, {4}, {4} | {}, {}, {} |];
array[1..5] of var 1..3: x;
constraint regular_nfa(x, Q, 3, d, 1, {4});
solve satisfy;
