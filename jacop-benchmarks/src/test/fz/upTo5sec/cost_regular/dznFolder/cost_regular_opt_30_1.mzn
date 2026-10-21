% Minimum cost word of a random cost automaton with a fixed number of 1s; optimum confirmed by Chuffed with the standard decomposition.
include "globals.mzn";
array[1..30] of var 1..4: x;
var 0..1000: c;
array[1..6,1..4] of 0..6: d = [|1,4,4,2|1,0,5,1|3,2,1,0|1,1,0,2|0,5,4,0|3,2,3,0|];
array[1..6,1..4] of int: w = [|6,8,1,2|4,1,5,8|6,8,3,4|4,9,7,8|6,9,0,7|3,6,6,2|];
constraint cost_regular(x, 6, 4, d, 1, 1..6, w, c);
constraint count(x, 1) = 10;
solve :: int_search(x, input_order, indomain_min) minimize c;
output ["x = \(x);\nc = \(c);\n"];
