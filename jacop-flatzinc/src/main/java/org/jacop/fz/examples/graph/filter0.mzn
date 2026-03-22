include "jacop.mzn";

enum types = {add, mul};

int: N = 7;  % number of edges in trgaet graph
int: M = 8;  % number of nodes in the target graph

int: P = 3; % number of nodes in the pattern graph
int: E = 2; % number of edges in the pattern graph

array[0..E-1, 0..1] of int: pattern_graph = array2d(0..E-1, 0..1, [0, 1, 1, 2]);
array[0..N-1, 0..1] of int: target_graph  = array2d(0..N-1, 0..1, [0, 4, 1, 5, 2, 6, 3, 6, 4, 5, 5, 7, 6, 7]);

array[0..M-1] of int: target_types  = array1d(0..M-1, [mul, mul, mul, mul, add, add, add, add]);
array[0..P-1] of int: pattern_types = array1d(0..P-1, [mul, add, add]);

array[0..P-1] of var 0..M-1: match;

constraint
   sub_digraph_match(target_graph, pattern_graph, target_types, pattern_types, match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]
