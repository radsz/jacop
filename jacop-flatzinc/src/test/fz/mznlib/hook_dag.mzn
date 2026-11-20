include "globals.mzn";
% dag on a 4-node graph with a 3-cycle, a 2-cycle, a self-loop and parallel edges. The standard
% decomposition lets an edge leave a node that is not selected; dag is documented on a subgraph,
% so both sides state that the selected edges select their nodes.
array[1..8] of int: f = [1, 2, 3, 3, 4, 4, 2, 1];
array[1..8] of int: t = [2, 3, 1, 4, 3, 4, 3, 2];
array[1..4] of var bool: ns;
array[1..8] of var bool: es;
constraint dag(f, t, ns, es);
constraint forall (e in 1..8) (es[e] -> ns[f[e]] /\ ns[t[e]]);
solve satisfy;
output ["ns=\(ns) es=\(es)\n"];
