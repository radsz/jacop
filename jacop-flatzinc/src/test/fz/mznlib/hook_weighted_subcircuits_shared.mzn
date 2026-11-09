% weighted_subcircuits with variables or constants shared between its arguments (the same
% variable in tour twice, equal constant tour costs).
include "weighted_subcircuits.mzn";
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
