% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Simple paths between nodes 1 and 6 of a 3x2 grid with a diagonal.
include "globals.mzn";
array[1..8] of int: from = [1, 2, 4, 5, 1, 2, 3, 1];
array[1..8] of int: to   = [2, 3, 5, 6, 4, 5, 6, 5];
array[1..6] of var bool: ns;
array[1..8] of var bool: es;
int: s = 1;
int: t = 6;
constraint path(6, 8, from, to, s, t, ns, es);
constraint sum(ns) >= 3;
solve satisfy;
