% Cross-checked regression test, from Hakan Kjellerstrand's /tmp/claude-0/-home-claude/71c00cd1-6f56-5413-a2d2-79940d8b2723/scratchpad/ext/hk/minizinc/max_flow_winston1.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% network_flow over the arc list instead of flow conservation sums
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Maximum flow problem from Winston "Operations Research", page 420
% (hakank/minizinc/max_flow_winston1.mzn), written with network_flow: the flow is a
% circulation with balance 0 at every node, and the return arc 5 -> 1 carries the
% flow that is maximised.
include "globals.mzn";

int: num_arcs = 7;
array[1..num_arcs, 1..2] of int: arcs = array2d(1..num_arcs, 1..2,
  [1, 2,
   1, 3,
   2, 3,
   2, 4,
   3, 5,
   4, 5,
   5, 1]);
array[1..num_arcs] of int: cap = [2, 3, 3, 4, 2, 1, 100];

array[1..num_arcs] of var 0..max(cap): flow;
constraint forall(a in 1..num_arcs)(flow[a] <= cap[a]);
var int: z = flow[num_arcs];

constraint network_flow(arcs, [0 | i in 1..5], flow);

solve :: seq_search([
    int_search(array1d(flow), input_order, indomain_min, complete)])
  maximize z;

output ["z: \(z)\n"] ++ [ "\(arcs[a, 1]) -> \(arcs[a, 2]): \(flow[a])\n" | a in 1..num_arcs ];
