%-----------------------------------------------------------------------------%
% JaCoP predicate subcircuit_cost: x is a subcircuit (x[i] = i when node i is
% left out) and cost = sum(i in index_set(x))(d[i, x[i]]). The diagonal d[i, i]
% is the cost of leaving node i out, 0 when that costs nothing.
%
% JaCoP posts subcircuit with SubcircuitCost, which bounds the cost with the
% assignment problem and the Steiner cycle bound of Vismara and Briot (CP 2018).
% The same filtering is added automatically when a model states
% subcircuit(x) /\ cost = sum(i)(d[i, x[i]]); the predicate makes it explicit.
%-----------------------------------------------------------------------------%
predicate subcircuit_cost(array[int] of var int: x, array[int,int] of int: d, var int: cost) =
  assert(index_set_1of2(d) = index_set(x) /\ index_set_2of2(d) = index_set(x),
         "subcircuit_cost: d must be indexed by the nodes of x in both dimensions",
    let { int: l = min(index_set(x)) } in
    if l = 1 then
      jacop_subcircuit_cost(x, array1d(d), cost)
    else
      jacop_subcircuit_cost([x[i] - l + 1 | i in index_set(x)], array1d(d), cost)
    endif);

predicate jacop_subcircuit_cost(array[int] of var int: x, array[int] of int: d, var int: cost);
