include "globals.mzn";
% regular_nfa with the alphabet given as a set of symbols.
array[1..4] of var 1..5: x;
constraint regular_nfa(x, 2, 2..4, array2d(1..2, 2..4, [{1, 2}, {}, {2}, {1}, {1, 2}, {}]), 1, {2});
solve satisfy;
