% Cross-checked regression test, written for the MiniZinc graph globals (org.jacop.constraints.graph).
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Minimum spanning tree with node degree at most 2 (a minimum Hamiltonian path).
include "globals.mzn";
int: N = 6; int: E = 11;
array[1..E] of int: from = [1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 2];
array[1..E] of int: to   = [2, 3, 4, 3, 5, 4, 6, 5, 6, 6, 6];
array[1..E] of int: w    = [4, 2, 6, 1, 7, 3, 5, 2, 8, 3, 9];
array[1..E] of var bool: es;
var 0..60: K;
constraint forall(v in 1..N)(sum(e in 1..E where from[e] = v \/ to[e] = v)(es[e]) <= 2);
constraint weighted_spanning_tree(N, E, from, to, w, es, K);
solve :: seq_search([
    int_search([K], input_order, indomain_min, complete),
    bool_search(array1d(es), input_order, indomain_min, complete)])
  minimize K;
