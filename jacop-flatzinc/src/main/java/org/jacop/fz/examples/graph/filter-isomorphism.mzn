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

set of int: index_set_edges = index_set_1of2(target_graph);
int: t_min = lb_array(target_graph);
int: t_max = ub_array(target_graph);
array[t_min..t_max] of set of int: et = array1d(t_min..t_max, [ {target_graph[j,2] | j in index_set_edges where target_graph[j,1] = i} | i in t_min..t_max]);

set of int: index_set_p_edges = index_set_1of2(pattern_graph);
int: p_min = lb_array(pattern_graph);
int: p_max = ub_array(pattern_graph);
array[p_min..p_max] of set of int: pt = array1d(p_min..p_max, [ {pattern_graph[j,2] | j in index_set_p_edges where pattern_graph[j,1] = i} | i in p_min..p_max]);


array[1..M] of int: target_types = [mul, mul, mul, mul, add, add, add, add];
array[1..P] of int: pattern_types = [mul, add, add];

array[1..P] of var 1..M: match;

constraint
   graph_isomorphism(et, pt, target_types, pattern_types, match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]
