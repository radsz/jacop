% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Directed simple paths from 1 to 5, nodes numbered from 1 with parallel arcs.
include "globals.mzn";
array[1..9] of int: from = [1, 1, 2, 2, 3, 3, 4, 2, 4];
array[1..9] of int: to   = [2, 3, 3, 4, 4, 5, 5, 4, 2];
array[1..5] of var bool: ns;
array[1..9] of var bool: es;
constraint dpath(from, to, 1, 5, ns, es);
solve satisfy;
