% Minimum cost word of a random cost automaton with a fixed number of 1s; optimum confirmed by Chuffed with the standard decomposition.
include "globals.mzn";
array[1..20] of var 1..4: x;
var 0..1000: c;
array[1..6,1..4] of 0..6: d = [|0,0,1,2|6,0,2,5|4,6,0,3|4,1,0,3|0,5,2,1|2,5,5,2|];
array[1..6,1..4] of int: w = [|7,6,8,5|9,5,5,7|2,6,7,8|3,7,4,7|8,8,5,7|7,5,9,8|];
constraint cost_regular(x, 6, 4, d, 1, 1..6, w, c);
constraint count(x, 1) = 6;
solve :: int_search(x, input_order, indomain_min) minimize c;
output ["x = \(x);\nc = \(c);\n"];
