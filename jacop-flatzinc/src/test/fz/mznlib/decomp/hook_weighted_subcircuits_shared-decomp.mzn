% The decomposition of weighted_subcircuits (see the JaCoP library comments).
include "alldifferent.mzn";
% every node i with next[i] != i belongs to tour[i] in 1..T, the nodes of one tour form one
% circuit, left out nodes have tour 0, tour_cost[k] sums d over tour k, cost over all nodes
predicate weighted_subcircuits(array[int] of var int: next, array[int] of var int: tour,
                               array[int,int] of int: d, array[int] of var int: tour_cost,
                               var int: cost) =
  let { set of int: N = index_set(next), int: n = card(N), set of int: T = index_set(tour_cost),
        array[N] of var 0..n: order } in
  all_different(next) /\
  forall(i in N)(next[i] in N /\ (next[i] = i <-> tour[i] = 0) /\ tour[i] in {0} union T) /\
  forall(i in N)(next[i] != i -> tour[next[i]] = tour[i]) /\
  % one circuit per tour: the smallest node of a tour has order 1, order grows along the circuit
  forall(i in N)(tour[i] = 0 <-> order[i] = 0) /\
  forall(i in N)(next[i] != i -> (order[next[i]] = order[i] + 1 \/ order[next[i]] = 1)) /\
  forall(i in N)(order[i] = 1 <-> (tour[i] > 0 /\ forall(j in N where j < i)(tour[j] != tour[i]))) /\
  forall(k in T)(tour_cost[k] = sum(i in N)(d[i, next[i]] * bool2int(tour[i] = k))) /\
  cost = sum(i in N)(d[i, next[i]]);
array[1..4, 1..4] of int: d = [| 1, 2, 1, 2 | 2, 1, 2, 1 | 1, 2, 1, 2 | 2, 1, 2, 1 |];
% shared variables: two nodes in the same tour, both tours of equal cost
array[1..4] of var 1..4: next;
array[1..4] of var 0..2: tour;
array[1..2] of var 0..12: tc;
var 0..20: cost;
constraint tour[1] = tour[2] /\ tc[1] = tc[2];
constraint weighted_subcircuits(next, tour, d, tc, cost);
% shared constants: both tour costs fixed to the same value, all tours of one node set fixed
array[1..3] of var 1..3: next2;
array[1..3] of var 0..2: tour2;
array[1..2] of var 0..9: tc2 :: no_output;
var 0..20: cost2;
constraint tc2[1] = 0 /\ tc2[2] = 0;
constraint weighted_subcircuits(next2, tour2, [| 1, 1, 1 | 1, 2, 1 | 1, 1, 1 |], tc2, cost2);
solve satisfy;
