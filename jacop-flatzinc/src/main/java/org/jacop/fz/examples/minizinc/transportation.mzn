%
% Factories produce components that are shipped to different markets. 
% Each factory can produces different number of components and each market 
% need a given number of components. Each connection from factory to a market
% has a cost per send unit and the goal is to minimize the cost of shipping 
% components while fulfilling markets needs.
%
% In the model below we assume three factories and four markets.
% The problem can be modeled by a network flow model where nodes 2, 3 and 4
% are factory nodes and nodes 5, 6 and 7 are marker nodes. Node 1 represents
% source and nodes 8, 9 an 10 sinks. Arcs are defined by array arc. The flow on 
% each arc can be between 0 and 5 (flow array). Array b represents the total flow
% of a node, i.e. difference between outgoing and incomming flow. Therefore node
% 1 produces flow 9 and each node 8, 9 and 10 consumes flow 3. Array unit_cost
% represents cost assigned of shipping one component between give factory and 
% the market.
%
% Author: Krzysztof Kuchcinski


include "networkflow.mzn";

int: n = 10;   % number of nodes
int: m = 13;  % number of arcs

array[1..m, 1..2] of int: arc =[| 1, 2 |
	    	     	       	  1, 3 |
				  1, 4 |
				  2, 5 |
				  2, 6 |
				  3, 5 |
				  3, 6 |
				  3, 7 |
				  4, 6 |
				  4, 7 |
				  5, 8 |
				  6, 9 |
				  7, 10
	    	     	         |];
array[1..m] of var 0..5 : flow;
array[1..m] of int: unit_cost = [ 0, 0, 0, 3, 1, 4, 2, 4, 3, 3, 0, 0, 0];
array[1..n] of int: b = [9, 0, 0, 0, 0, 0, 0, -3, -3, -3];

var int: cost;

constraint
	flow[2] <= 3 /\ flow[3] <= 3 /\
	flow[11] = 3 /\ flow[12] = 3 /\ flow[13] = 3 /\
	networkflow(arc, flow, unit_cost, b, cost);

solve minimize cost;

output(["Flow on arcs\n"]++
[show(arc[i,1])++" --> "++show(arc[i,2])++" = "++show(flow[i])++"\n" | i in 1..m] ++
["cost = "++show(cost)++"\n"])