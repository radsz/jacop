include "jacop.mzn";

int: N = 30;  % number of edges
int: M = 20;  % number of nodes

array[0..N-1, 1..2] of int: target_graph = array2d(0..N-1, 1..2, [ 0, 12,
								   0, 15,
								   1, 11,
								   1, 19,
								   2, 10,
								   3, 0,
								   3, 4,
								   5, 2,
								   6, 8,
								   6, 19,
								   7, 6,
								   8, 14,
								   8, 17,
								   9, 7,
								   9, 11,
								   9, 19,
								   10, 17,
								   12, 5,
								   12, 13,
								   13, 2,
								   13, 3,
								   14, 7,
								   14, 10,
								   15, 4,
								   16, 11,
								   16, 15,
								   17, 5,
								   18, 1,
								   18, 4,
								   18, 16]);
array[0..N-1, 1..2] of int: pattern_graph = array2d(0..N-1, 1..2, [ 0, 3,
								    1, 4,
								    1, 17,
								    2, 15,
								    3, 7,
								    3, 9,
								    4, 5,
								    6, 8,
								    6, 15,
								    8, 5,
								    8, 14,
								    9, 12,
								    9, 16,
								    10, 0,
								    10, 7,
								    10, 17,
								    11, 7,
								    11, 17,
								    12, 2,
								    13, 12,
								    14, 4,
								    14, 19,
								    15, 13,
								    16, 0,
								    16, 13,
								    18, 1,
								    18, 5,
								    18, 11,
								    19, 2,
								    19, 6]);


array[0..M-1] of var 0..M-1: match;

set of int: index_set_edges = index_set_1of2(target_graph);
int: t_min = lb_array(target_graph);
int: t_max = ub_array(target_graph);
array[t_min..t_max] of set of int: et = array1d(t_min..t_max, [ {target_graph[j,2] | j in index_set_edges where target_graph[j,1] = i} | i in t_min..t_max]);

set of int: index_set_p_edges = index_set_1of2(pattern_graph);
int: p_min = lb_array(pattern_graph);
int: p_max = ub_array(pattern_graph);
array[p_min..p_max] of set of int: pt = array1d(p_min..p_max, [ {pattern_graph[j,2] | j in index_set_p_edges where pattern_graph[j,1] = i} | i in p_min..p_max]);

constraint
  graph_isomorphism(pt, et, match);
  % digraph_match(target_graph, pattern_graph, array1d(0..N-1, [1 | i in 0..N-1]),
  %               array1d(0..N-1, [1 | i in 0..N-1]), match);

solve :: int_search(match, input_order, indomain_min) satisfy;

output["match = \(match)"]
