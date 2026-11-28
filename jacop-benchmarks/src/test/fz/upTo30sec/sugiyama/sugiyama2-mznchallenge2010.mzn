%=============================================================================
%
% Optimal ordering layout for a Sugiyami style graph.
%
% This version of the model appeared in the MiniZinc Challenge 2010, but it is
% now deprecated in favour of sugiyama2.mzn .
%
%=============================================================================

include "globals.mzn";

% parameters

int: layers; %% number of graph layers
set of int: Layers = 1.. layers;
array[Layers] of int: width; %% number of nodes on each level;

int: nodes; %% total number of nodes;
set of int: Nodes = 1..nodes;

constraint assert(nodes == sum(i in Layers)(width[i]), "nodes must equal the sum of the widths");

array[Layers] of set of int: Lnodes = 
   [ 1 + sum(i in 1..l-1)(width[i]) .. sum(i in 1..l)(width[i]) | l in Layers ];

int: edges; % number of edges
set of int: Edges = 1..edges; 

array[Edges] of Nodes: start; % start of edge 
array[Edges] of Nodes: end; % end of edge

array[Nodes] of set of Nodes: startNodes =
    [{start[e] | e in Edges where end[e] = n} | n in Nodes];
array[Nodes] of set of Nodes: endNodes =
    [{end[e] | e in Edges where start[e] = n} | n in Nodes];

int: nbFullyConnected = 
    length([true | n1 in Nodes, n2 in endNodes[n1],
                   n3 in startNodes[n2] intersect ((n1 + 1) .. nodes),
                   n4 in endNodes[n1] intersect endNodes[n3] where n2 < n4]);

array[1..nbFullyConnected] of set of int: fullyConnected = 
    [{n1,n2,n3,n4} | n1 in Nodes, n2 in endNodes[n1],
                     n3 in startNodes[n2] intersect ((n1 + 1) .. nodes),
                     n4 in endNodes[n1] intersect endNodes[n3] where n2 < n4];

array[Layers] of int: partial_widths = [sum([width[i]  | i in 1 .. (l - 1)]) | l in 1..layers];

% variables

array[Nodes] of var 1..nodes: positions;

constraint forall(l in Layers, n in Lnodes[l])(positions[n] > partial_widths[l] /\
    positions[n] <= partial_widths[l] + width[l]);

constraint forall(l in Layers)(all_different([positions[n] | n in Lnodes[l]]));

set of int: crossingsSet = 
    {e1 + (e2 - 1) * edges | 
            l in 1.. (layers - 1), e1 in Edges, e2 in (e1 + 1) .. edges where
            start[e1] != start[e2] /\ end[e1] != end[e2] /\
            start[e1] in Lnodes[l] /\ start[e2] in Lnodes[l] /\
            not(exists(i in 1..nbFullyConnected)(fullyConnected[i] =
                {start[e1],start[e2],end[e1],end[e2]}))}; 

int: maxCrossings = card(crossingsSet); 

array[1..maxCrossings] of int: crossingsE1 =
    [((c - 1) mod edges) + 1 | c in crossingsSet];
array[1..maxCrossings] of int: crossingsE2 =
    [((c - 1) div edges) + 1 | c in crossingsSet];

array[1..maxCrossings] of var 0..1: crossings =
    [ bool2int(positions[start[crossingsE1[c]]] < positions[start[crossingsE2[c]]] /\
               positions[end[crossingsE2[c]]] < positions[end[crossingsE1[c]]]) +
      bool2int(positions[start[crossingsE2[c]]] < positions[start[crossingsE1[c]]] /\
               positions[end[crossingsE1[c]]] < positions[end[crossingsE2[c]]]) |
        c in 1 .. maxCrossings];

var 0..maxCrossings: nbCrossings = sum(crossings);

% put unconnected nodes first on each layer
array[Layers] of set of int: unconnected = [{n | n in Lnodes[l] where startNodes[n] = {} /\ endNodes[n] = {}} | l in Layers];

constraint forall(l in Layers, i in 1..card(unconnected[l]))(positions[unconnected[l][i]] = partial_widths[l] + i);

constraint forall(l in Layers)(forall(n1 in Lnodes[l], n2 in Lnodes[l] where n1 != n2 /\ (endNodes[n1] = {} \/ endNodes[n2] = {}) /\
    card(startNodes[n1] intersect startNodes[n2]) <= 1 /\ 
    card(startNodes[n1] union startNodes[n2]) > 1 /\ startNodes[n1] != {} /\ startNodes[n2] != {})(
    forall(n3 in startNodes[n1], n4 in startNodes[n2] where n3 != n4)(positions[n3] < positions[n4]) -> positions[n1] < positions[n2]));

constraint forall(l in Layers)(forall(n1 in Lnodes[l], n2 in Lnodes[l] where n1 != n2 /\ (startNodes[n1] = {} \/ startNodes[n2] = {}) /\
    card(endNodes[n1] intersect endNodes[n2]) <= 1 /\
    card(endNodes[n1] union endNodes[n2]) > 1 /\ endNodes[n1] != {} /\ endNodes[n2] != {})(
    forall(n3 in endNodes[n1], n4 in endNodes[n2] where n3 != n4)(positions[n3] < positions[n4]) -> positions[n1] < positions[n2]));

solve :: int_search(positions, input_order, indomain_min, complete) minimize nbCrossings;

output ["Number of crossings: ", show(nbFullyConnected + nbCrossings), "\nPositions: ", show(positions), "\n"];
