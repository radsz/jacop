% Cross-checked regression test, from Hakan Kjellerstrand's /tmp/claude-0/-home-claude/71c00cd1-6f56-5413-a2d2-79940d8b2723/scratchpad/ext/hk/minizinc/transportation2.mzn
% (https://github.com/radsz/hakank/tree/master/minizinc).
% network_flow_cost with a dummy client for unused capacity; capacities and demands divided by 100
% Search annotation made input_order/indomain_min on all decision variables, so
% every solver reaches the same solution.
% Transportation problem (hakank/minizinc/transportation2.mzn), written with
% network_flow_cost. Plants supply their capacity, clients consume their demand,
% and a dummy client takes the unused capacity at no cost. Capacities and demands
% are those of the original divided by 100, so that Gecode and Chuffed can prove
% optimality for the cross-check.
include "globals.mzn";

int: num_plants = 3;
int: num_clients = 4;
array[1..num_plants] of int: capacity = [5, 3, 4];
array[1..num_clients] of int: demand = [2, 4, 3, 1];
array[1..num_plants, 1..num_clients] of int: cost = [|10, 8, 5, 9,
                                                       |7, 5, 5, 3,
                                                       |11,10, 8, 7|];

int: dummy = num_plants + num_clients + 1;
int: slack = sum(capacity) - sum(demand);
array[1..num_plants * (num_clients + 1), 1..2] of int: arcs =
  array2d(1..num_plants * (num_clients + 1), 1..2,
    [ if k = 1 then i elseif j <= num_clients then num_plants + j else dummy endif
    | i in 1..num_plants, j in 1..num_clients + 1, k in 1..2 ]);
array[1..dummy] of int: balance =
  capacity ++ [ -demand[j] | j in 1..num_clients ] ++ [ -slack ];
array[1..num_plants * (num_clients + 1)] of int: weight =
  [ if j <= num_clients then cost[i, j] else 0 endif | i in 1..num_plants, j in 1..num_clients + 1 ];

array[1..num_plants, 1..num_clients] of var 0..max(demand): x;
array[1..num_plants] of var 0..slack: unused;
var 0..sum(i in 1..num_plants)(capacity[i] * max(j in 1..num_clients)(cost[i, j])): z;

constraint forall(i in 1..num_plants, j in 1..num_clients)(x[i, j] <= demand[j]);
constraint network_flow_cost(arcs, balance, weight,
  [ if j <= num_clients then x[i, j] else unused[i] endif | i in 1..num_plants, j in 1..num_clients + 1 ], z);

solve :: seq_search([
    int_search([x[i, j] | i in 1..num_plants, j in 1..num_clients], input_order, indomain_min, complete),
    int_search(array1d(x) ++ array1d(unused) ++ [z], input_order, indomain_min, complete)])
  minimize z;

output ["x: \(x)\nz: \(z)\n"];
