%-----------------------------------------------------------------------------%
% JaCoP predicate weighted_subcircuits (Vismara and Briot, CP 2018): up to
% length(tour_cost) disjoint circuits cover part of the nodes.
%   next[i]       the successor of node i, i itself when node i is left out;
%   tour[i]       the circuit of node i, 1..length(tour_cost), or 0 when left out;
%   tour_cost[k]  the sum of d[i, next[i]] over the nodes of circuit k;
%   cost          the sum of d[i, next[i]] over all nodes, so d[i, i] is the
%                 cost of leaving node i out.
% The nodes of each circuit form one circuit (or none), and the successors are
% all different.
%-----------------------------------------------------------------------------%
predicate weighted_subcircuits(array[int] of var int: next, array[int] of var int: tour,
                               array[int,int] of int: d, array[int] of var int: tour_cost,
                               var int: cost) =
  assert(index_set(tour) = index_set(next) /\ index_set_1of2(d) = index_set(next)
         /\ index_set_2of2(d) = index_set(next),
         "weighted_subcircuits: tour and d must be indexed by the nodes of next",
    jacop_weighted_subcircuits(next, tour, array1d(d), tour_cost, cost, min(index_set(next))));

predicate jacop_weighted_subcircuits(array[int] of var int: next, array[int] of var int: tour,
                                     array[int] of int: d, array[int] of var int: tour_cost,
                                     var int: cost, int: offset);
