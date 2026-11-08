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
