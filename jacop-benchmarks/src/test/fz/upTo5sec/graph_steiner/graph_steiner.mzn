% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Minimum Steiner tree joining terminals 1, 6 and 8 of a 9-node graph.
include "globals.mzn";
int: N = 9; int: E = 14;
array[1..E] of int: from = [1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8];
array[1..E] of int: to   = [2, 4, 3, 5, 6, 5, 5, 7, 6, 8, 9, 8, 1, 9];
array[1..E] of int: w    = [3, 2, 4, 1, 5, 3, 2, 6, 2, 4, 1, 3, 7, 2];
array[1..N] of var bool: ns;
array[1..E] of var bool: es;
var 0..60: K;
constraint ns[1] /\ ns[6] /\ ns[8];
constraint steiner(N, E, from, to, w, ns, es, K);
solve :: seq_search([
    int_search([K], input_order, indomain_min, complete),
    bool_search(array1d(ns) ++ array1d(es), input_order, indomain_min, complete)])
  minimize K;
