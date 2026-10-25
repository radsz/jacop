% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Connected subgraphs of a 5-node graph with a chord and a pendant node.
include "globals.mzn";
array[1..6] of int: from = [1, 2, 3, 4, 1, 4];
array[1..6] of int: to   = [2, 3, 4, 1, 3, 5];
array[1..5] of var bool: ns;
array[1..6] of var bool: es;
constraint connected(from, to, ns, es);
constraint ns[2] \/ ns[5];
solve satisfy;
