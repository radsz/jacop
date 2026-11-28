% Cross-checked regression test, from Hakan Kjellerstrand's /tmp/claude-0/-home-claude/71c00cd1-6f56-5413-a2d2-79940d8b2723/scratchpad/ext/hk/minizinc/max_flow_taha.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% network_flow over the arc list instead of flow conservation sums
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Maximum flow problem from Taha "Introduction to Operations Research", page 354
% (hakank/minizinc/max_flow_taha.mzn), written with network_flow_cost: a return
% arc from the sink to the source with weight -1 turns maximum flow into a
% minimum-cost circulation.
include "globals.mzn";

int: n = 5;
int: start = 1;
int: end = 5;
array[1..n, 1..n] of int: c = array2d(1..n, 1..n,
[
 0, 20, 30, 10,  0,
 0,  0, 40,  0, 30,
 0,  0,  0, 10, 20,
 0,  0,  5,  0, 20,
 0,  0,  0,  0,  0
]);

set of int: Arcs = 1..m;
int: m = card({k | k in 1..n*n where c[(k-1) div n + 1, (k-1) mod n + 1] > 0}) + 1;
array[1..m - 1, 1..2] of int: cap_arcs = array2d(1..m - 1, 1..2,
  [ if j = 1 then i else k endif | i, k in 1..n where c[i, k] > 0, j in 1..2 ]);
array[Arcs, 1..2] of int: arcs = array2d(Arcs, 1..2,
  [ if a < m then cap_arcs[a, j] elseif j = 1 then end else start endif | a in Arcs, j in 1..2 ]);
array[Arcs] of int: weight = [ if a < m then 0 else -1 endif | a in Arcs ];
int: cap_out = sum(k in 1..n)(c[start, k]);

array[Arcs] of var 0..cap_out: flow;
constraint forall(a in 1..m - 1)(flow[a] <= c[arcs[a, 1], arcs[a, 2]]);
var -cap_out..0: cost;

constraint network_flow_cost(arcs, [0 | i in 1..n], weight, flow, cost);

solve :: seq_search([
    int_search(array1d(flow) ++ [cost], input_order, indomain_min, complete)])
  minimize cost;

output ["total: \(-cost)\n"] ++
       [ "\(arcs[a, 1]) -> \(arcs[a, 2]): \(flow[a])\n" | a in 1..m - 1 ];
