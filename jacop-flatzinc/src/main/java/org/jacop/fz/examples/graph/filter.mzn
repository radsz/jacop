include "jacop.mzn";

enum types = {add, mul};

int: N = 7;  % number of edges in trgaet graph
int: M = 8;  % number of nodes in the target graph

int: P = 3; % number of nodes in the pattern graph
int: E = 2; % number of edges in the pattern graph

array[1..E, 1..2] of int: pattern_graph = [| 1, 2
					   | 2, 3|];

array[1..N, 1..2] of int: target_graph = [| 1, 5
					  | 2, 6
					  | 3, 7
					  | 4, 7
					  | 5, 6
					  | 6, 8
					  | 7, 8 |];

array[1..M] of int: target_types = [mul, mul, mul, mul, add, add, add, add];
array[1..P] of int: pattern_types = [mul, add, add];

array[1..P] of var 1..M: match;

constraint
   sub_digraph_match(target_graph, pattern_graph, target_types, pattern_types, match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]
