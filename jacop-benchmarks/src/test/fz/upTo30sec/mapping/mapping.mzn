% Model for mapping H263 encoder on a system with a network on chip (NoC)
%
% The model is a simplified version of the model presented in the paper
%
% "Mapping streaming applications on multiprocessors with time-division-multiplexed network-on-chip ",
% by
% Usman Mazhar Mirza, Flavius Gruian and Krzysztof Kuchcinski,
% Computers & Electrical Engineering, vol. 40, no. 8, pp. 276-291, 2014
%
% Author: Krzysztof Kuchcinski

include "globals.mzn";

int: row;          % number of rows in the mesh
int: col;          % number of columns in the mesh
int: k = row*col;  %  number processors
int: n = k + 2;    % number of nodes
int: no_links;     % number of links between processors
int: m = no_links + 2*k;  % number of arcs
int: no_flows;     % number of flows
int: link_bandwidth;

int: no_actors;

array[1..m, 1..2] of int: arc;

array[1..m] of int: unit_cost;

array[1..no_flows, 1..n] of int: balance;

int: processor_load;
array[1..k] of var 0..processor_load: cpu_loads;

array[1..no_actors] of int: actor_load;
array[1..2, 1..no_flows] of int: load;

array[1..no_flows] of var 0..10000: cost;

% var 0..10000: load_cost;
% var 0..10000: cpu_cost;
var 0..10000: communication_cost;
var 0..10000: objective;

array[1..2*no_flows] of var 1..k: flow_processor;

array[1..no_links] of var 0..link_bandwidth : comm_full;
array[1..k] of var 0..5*link_bandwidth : flow_from_processor;

array[1..k] of var 0..10000*no_flows: cc;

array[1..no_flows] of int: inStream;
array[1..no_flows, 1..n] of int: b;

array[1..no_flows, 1..k] of var 0..max(inStream): inFlow;
array[1..no_flows, 1..k] of var 0..max(inStream): outFlow;
array[1..no_flows, 1..no_links] of var 0..link_bandwidth: commFlow;

array[1..no_flows, 1..m] of var 0..max(max(inStream),link_bandwidth): flows;

array[1..no_flows,1..2] of int: source_destination_actor;

array[1..no_actors] of var 1..k: actor_processor;

array[1..2*k*no_flows + no_links] of var 0..max(max(inStream),link_bandwidth): total_flow;
array[1..2*k*no_flows + no_links] of int: total_unit_cost;
array[1..k+2*no_flows] of int: total_balance;

array[1..2*no_flows*k] of int: in_connections;
array[1..2*no_flows*k] of int: out_connections;
array[1..2*no_flows*k+no_links, 1..2] of int: all_connections;

%% === Model constraints ===

constraint %% constraining input and output flows defining mapping
   forall( i in 1..no_flows, j in 1..k) (inFlow[i,j] in {0, inStream[i]} /\ outFlow[i,j] in {0, inStream[i]})
;

constraint %% to select processor and not divide flow on incomming and outgoing streams
	forall (i in 1..no_flows) (count([flows[i,j] | j in 1..k], 0, k-1) /\ count([flows[i,j] | j in m-k+1..m], 0, k-1))
;

constraint %% network flow constraint
	forall (i in 1..no_flows) (network_flow_cost(arc,  [balance[i,j] | j in 1..n], unit_cost, [flows[i,j] | j in 1..m], cost[i]))
;

constraint  %% networkflow for all flows
	network_flow_cost(all_connections, total_balance, total_unit_cost, total_flow, communication_cost)
	/\
	%% flow for communications between processors for the combined network flow; must be the same as sum of separate flows
	forall (i in 1..no_links) (comm_full[i] = sum(j in 1..no_flows)(flows[j,i+k]))
;

constraint %% computes processors' load
	forall (i in 1..no_flows, j in 1..k) ( ( flows[i,j] != 0 <-> flow_processor[i] = j)
	       	     		               /\
				               ( flows[i, m-k+j] != 0 <-> flow_processor[no_flows+i] = j) )
	/\ 
	bin_packing_load(cpu_loads, flow_processor, [load[i, j] | i in 1..2, j in 1..no_flows])
;

constraint  %% cost function to minimize
	forall (i in 1..k) (cc[i] = sum(j in 1..no_flows)((flow_processor[source_destination_actor[j,1]] = i) * cost[j]))
	/\
	maximum(objective, [cpu_loads[i] + cc[i] | i in 1..k])
	% maximum(load_cost, [cpu_loads[i] + cc[i] | i in 1..k])
	% /\
	% objective = load_cost
;

constraint  %% flow out from each processor
	    forall (i in 1..k) (flow_from_processor[i] = sum(j in 1..no_flows, n in k+1..no_links+k where arc[n,1] = i) (flows[j,n]))
;

% constraints on flow_processors; to be the same if they are the same as source or sink
constraint
	forall ( i in 1..no_flows) ( 
	       forall (j in i+1..no_flows where source_destination_actor[i,1] = source_destination_actor[j,1]) (flow_processor[i] = flow_processor[j]))
	/\
	forall ( i in 1..no_flows) ( 
	       forall (j in 1..no_flows where source_destination_actor[i,1] = source_destination_actor[j,2]) (flow_processor[i] = flow_processor[no_flows+j]))
	/\
	forall ( i in 1..no_flows) ( 
	       forall (j in i+1..no_flows where source_destination_actor[i,2] = source_destination_actor[j,2]) (flow_processor[no_flows+i] = flow_processor[no_flows+j]))
;

solve :: seq_search([
            int_search(flow_processor, first_fail, indomain_min, complete),
      	    int_search(total_flow, smallest, indomain_min, complete),
      	    int_search(cost ++ [communication_cost], input_order, indomain_min, complete)
          , int_search( cpu_loads, first_fail, indomain_min, complete)
          , int_search( [inFlow[i,j] | i in 1..no_flows, j in 1..k], first_fail, indomain_min, complete)
          , int_search( [outFlow[i,j] | i in 1..no_flows, j in 1..k], first_fail, indomain_min, complete)
          , int_search( [commFlow[i,j] | i in 1..no_flows, j in 1..no_links], first_fail, indomain_min, complete)
          , int_search( [flows[i,j] | i in 1..no_flows, j in 1..m], first_fail, indomain_min, complete)
          , int_search( actor_processor, first_fail, indomain_min, complete)

      ]) 
      minimize objective;

array[1..no_links] of string: link_str;

% output
% ["Objective = " ++ show(objective) ++ ", Communication_cost = " ++  show(communication_cost) ++ "\n" ++ "Processor loads = " ++ show(cpu_loads) ++"\n"] ++

% ["cpu for actor "++ show(i)++" = " ++ show(actor_processor[i]) ++", " | i in 1..no_actors] ++ ["\n"] ++

% [if i = 1 then "Flow " ++ show(j) ++ " with cost " ++ show(cost[j]) ++ " from processor "++ show(actor_processor[source_destination_actor[j,1]]) ++ " to " ++ show(actor_processor[source_destination_actor[j,2]]) ++ " :\n" ++ 
% if fix(cost[j]) != 0 then 
% if fix(flows[j,i+k]) != 0 then link_str[i] ++ show(flows[j,i+k]) ++ "\n" else "" endif else "" endif
% else
% if fix(flows[j,i+k]) != 0 then link_str[i] ++ show(flows[j,i+k]) ++ "\n" else "" endif endif | j in 1..no_flows, i in 1..no_links] 
% ;
%
output [ 
    "objective = \(objective);\n",
    "communication_cost = \(communication_cost);\n",
    "flow_processor = \(flow_processor);\n",
    "constraint total_flow = \(total_flow);\n",
    "cpu_loads = \(cpu_loads);\n",
    "inFlow = array2d(1..\(no_flows), 1..\(k), \(inFlow));\n",
    "outFlow = array2d(1..\(no_flows), 1..\(k), \(outFlow));\n",
    "commFlow = array2d(1..\(no_flows), 1..\(no_links), \(commFlow));\n",
    "constraint flows = array2d(1..\(no_flows), 1..\(m), \(flows));\n",
    "constraint actor_processor = \(actor_processor);\n"
];

