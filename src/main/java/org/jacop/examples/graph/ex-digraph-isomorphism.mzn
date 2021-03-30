include "jacop.mzn";

int: N = 30;  % number of edges
int: M = 20;  % number of nodes

array[1..N, 1..2] of int: target_graph = [| 1, 13
				| 1, 16
				| 2, 12
				| 2, 20
				| 3, 11
				| 4, 1
				| 4, 5
				| 6, 3
				| 7, 9
				| 7, 20
				| 8, 7
				| 9, 15
				| 9, 18
				| 10, 8
				| 10, 12
				| 10, 20
				| 11, 18
				| 13, 6
				| 13, 14
				| 14, 3
				| 14, 4
				| 15, 8
				| 15, 11
				| 16, 5
				| 17, 12
				| 17, 16
				| 18, 6
				| 19, 2
				| 19, 5
				| 19, 17|];
array[1..N, 1..2] of int: pattern_graph = [| 1, 4
				 | 2, 5
				 | 2, 18
				 | 3, 16
				 | 4, 8
				 | 4, 10
				 | 5, 6
				 | 7, 9
				 | 7, 16
				 | 9, 6
				 | 9, 15
				 | 10, 13
				 | 10, 17
				 | 11, 1
				 | 11, 8
				 | 11, 18
				 | 12, 8
				 | 12, 18
				 | 13, 3
				 | 14, 13
				 | 15, 5
				 | 15, 20
				 | 16, 14
				 | 17, 1
				 | 17, 14
				 | 19, 2
				 | 19, 6
				 | 19, 12
				 | 20, 3
				 | 20, 7|];


array[1..M] of var 1..M: match;

% set of int: index_set_edges = index_set_1of2(target_graph);
% int: t_min = lb_array(target_graph);
% int: t_max = ub_array(target_graph);
% array[t_min..t_max] of set of int: et = [ {target_graph[j,2] | j in index_set_edges where target_graph[j,1] = i} | i in t_min..t_max];

% set of int: index_set_p_edges = index_set_1of2(pattern_graph);
% int: p_min = lb_array(pattern_graph);
% int: p_max = ub_array(pattern_graph);
% array[p_min..p_max] of set of int: pt = [ {pattern_graph[j,2] | j in index_set_p_edges where pattern_graph[j,1] = i} | i in p_min..p_max];

constraint
%  graph_isomorphism(pt, et, match);
  graph_isomorphism(pattern_graph, target_graph, match);
%  digraph_match(target_graph, pattern_graph, match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]
