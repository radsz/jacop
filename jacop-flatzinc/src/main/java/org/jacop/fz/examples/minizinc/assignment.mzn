% The assignment problem is to assign a set of people to a set of
% tasks. Each person needs a number of minutes to carry out a given
% task or a person cannot carry out a particular task.  Each person can
% be assigned to exactly one task.
%
% In the following problem we assume four persons and four tasks.
% Nodes 1, 2, 3 and 4 represent persons and nodes 5, 6, 7, and 8
% tasks. Array arc defines which tasks can be carried out by which
% persons. For example, person 1 can carry out tasks 6, 7 and 8 but
% not 5. Vector b defines a condition that each person is assigned to
% one task, i.e. out flow from a person is 1 and inflow for tasks is
% also 1 (-1 to depict inflow). Time for carrying out a task is
% defined by vector unit_cost.
%
% Author: Krzysztof Kuchcinski


include "networkflow.mzn";

int: n = 8;   % number of nodes
int: m = 12;  % number of arcs

array[1..m, 1..2] of int: arc =[| 1, 6 |
				  1, 7 |
				  1, 8 |
				  2, 5 |
				  2, 6 |
				  2, 7 |
				  3, 5 |
				  3, 7 |
				  3, 8 |
				  4, 5 |
				  4, 7 |
				  4, 8
	    	     	         |];
array[1..m] of var 0..1 : flow;
array[1..m] of int: unit_cost = [ 9, 7, 13, 16, 13, 8, 10, 6, 15, 11, 13, 17];
array[1..n] of int: b = [1, 1, 1, 1, -1, -1, -1, -1];

var int: cost;

constraint
	networkflow(arc, flow, unit_cost, b, cost);

solve minimize cost;

output ["Flow = "++ show(flow[i]) ++ " on arc (" ++ show(arc[i,1])++", "++show(arc[i,2])++")\n"| i in 1..m ]++["cost = "++show(cost)++"\n"]