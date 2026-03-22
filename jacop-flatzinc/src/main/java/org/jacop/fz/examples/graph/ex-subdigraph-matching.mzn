include "jacop.mzn";

int: N = 42;  % number of edges
int: M = 20;  % number of nodes

array[1..3, 1..2] of int: pattern_graph = [| 1, 2
					  | 2, 3
					  | 4, 3|];
array[1..N, 1..2] of int: target_graph = [| 1, 5
					   | 1, 8
					   | 1, 17
					   | 2, 4
					   | 2, 11
					   | 3, 4
					   | 3, 7
					   | 3, 12
					   | 3, 13
					   | 3, 15
					   | 4, 1
					   | 4, 6
					   | 4, 8
					   | 4, 9
					   | 4, 14
					   | 5, 16
					   | 5, 20
					   | 6, 10
					   | 6, 18
					   | 8, 3
					   | 8, 9
					   | 9, 2
					   | 9, 15
					   | 10, 8
					   | 10, 9
					   | 10, 12
					   | 10, 20
					   | 11, 1
					   | 11, 3
					   | 11, 6
					   | 11, 8
					   | 11, 13
					   | 14, 12
					   | 14, 19
					   | 15, 4
					   | 15, 12
					   | 17, 8
					   | 18, 15
					   | 19, 7
					   | 19, 12
					   | 20, 10
					   | 20, 13|];

array[1..4] of var 1..M: match;

constraint
  sub_digraph_match(target_graph, pattern_graph, match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]

