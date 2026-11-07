include "globals.mzn";
% regular_nfa on Regular: state 1 has three successors with symbol 1.
array[1..4] of var 0..4: x;
constraint regular_nfa(x, 3, 3,
  array2d(1..3, 1..3, [{1, 2, 3}, {1, 3}, {2, 3}, {1, 3}, {2}, {1, 2, 3}, {1}, {}, {}]), 1, {1, 2});
solve satisfy;
