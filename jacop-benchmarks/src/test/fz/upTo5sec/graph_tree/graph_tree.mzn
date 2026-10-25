% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Spanning and partial trees of a wheel graph containing node 1.
include "globals.mzn";
array[1..8] of int: from = [1, 1, 1, 1, 2, 3, 4, 5];
array[1..8] of int: to   = [2, 3, 4, 5, 3, 4, 5, 2];
array[1..5] of var bool: ns;
array[1..8] of var bool: es;
constraint tree(5, 8, from, to, 1, ns, es);
constraint sum(ns) >= 4;
solve satisfy;
