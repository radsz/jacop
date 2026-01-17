include "globals.mzn";

%------------------------------------------------------------------------------%
% Parameters

par int: nbOrders;
par int: nbColours;

par set of int: sizes;

array[int] of par int: ordSize;
array[int] of par int: ordCol;

par int: nbSlabs = nbOrders;

%------------------------------------------------------------------------------%
% Variables

array[1..nbOrders] of var 1..nbSlabs: assign;

array[int] of par int: order = arg_sort(ordSize);

array[int] of var 1..nbSlabs: ordered = [ assign[order[nbOrders-p+1]] | p in 1..nbOrders ];

constraint forall(i in 1..nbSlabs) (
  sum([ bool2int(exists(o in 1..nbOrders where ordCol[o]=c)(assign[o] = i)) | c in 1..nbColours ]) <= 2
  );

array[1..nbSlabs] of var 0..max(sizes): loads = bin_packing_load(assign, [ordSize[i] | i in 1..nbOrders]);

array[0..max(sizes)] of par int: frees = 
  array1d(0..max(sizes), [min([c - l | c in sizes where c >= l]) | l in 0..max(sizes)]);


constraint symmetry_breaking_constraint(
  forall(i in 1..nbSlabs-1) (loads[i] = 0 -> loads[i+1] = 0));
  
constraint symmetry_breaking_constraint(
  forall(i in 1..nbOrders, j in 1..nbOrders where j > i)(
    (ordSize[i] = ordSize[j] /\ ordCol[i] = ordCol[j]) -> assign[i] <= assign[j]));

int: objub = max(frees)*nbSlabs;
var 0..objub: objective;

constraint objective = sum(j in 1..nbSlabs)(frees[loads[j]]);

solve 
    :: int_search(ordered, first_fail, indomain_min, complete) 
    minimize objective;

output [ 
    "assign = \(assign);\n",
    "objective = \(objective);\n",
];
