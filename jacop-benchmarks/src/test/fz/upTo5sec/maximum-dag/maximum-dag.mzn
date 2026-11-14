%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Maximum Directed Acyclic Graph
% 
% Given a directed graph G=(V,E) find the subgraph of G that is a DAG. 
% Maximize the number of edges in the DAG.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% DZN info:
%% Files are named: xx_yy.dzn where xx is the number of nodes in G and 
%% yy is the index of the benchmark.

int: nbE;                      %Number of edges
int: nbV;                      %number of nodes
set of int: edges = 1..nbE;
set of int: nodes = 1..nbV;

%Directed graph: edges go from tail to head (tl ---> hd)
array[nodes,edges] of bool: incident; % incident[n,e] <-> n is e's head
array[nodes,edges] of bool: outgoing; % outgoing[n,e] <-> n is e's tail
array[edges] of int: tails;
array[edges] of int: heads;
array[1..2,edges] of int: endpairs = array2d(1..2,edges,tails++heads);


var 0..nbE: objective; %Total weight

array[edges] of var bool: chosen;     % edges selected to be in DAG
array[nodes] of var 0..nbE: distance; % distance from root
int: root = 1; %Node 1 is conencted to all other nodes
constraint distance[root] = 0;
constraint forall(a in nodes where a != root)(
    distance[a] = max( [ (distance[tails[b]] + 1)*chosen[b] 
                       | b in edges where incident[a,b]
                       ])
    );
constraint objective = sum (e in edges) (chosen[e]);

solve 
    :: seq_search([
        bool_search(chosen, input_order, indomain_max, complete),
        int_search(distance, input_order, indomain_min, complete)
    ])
    maximize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "chosen = ", show(chosen), ";\n",
    "distance = ", show(distance), ";\n",
    "objective = ", show(objective), ";\n"
];

%------------------------------------------------------------------------------%

