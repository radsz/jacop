% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Subgraphs of a digraph reachable from a variable root, nodes numbered from 0.
include "globals.mzn";
array[1..6] of int: from = [0, 1, 2, 2, 3, 0];
array[1..6] of int: to   = [1, 2, 0, 3, 1, 3];
array[0..3] of var bool: ns;
array[1..6] of var bool: es;
var 0..3: r;
constraint dreachable(from, to, r, ns, es);
constraint sum(es) <= 3;
solve satisfy;
