%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Diameter Constrained Minimum Spanning Tree
% 
% Given an undirected graph G=(V,E) and an integer D find a spanning 
% tree of G of minimum cost such that its diameter is not greater than 
% D.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% DZN info:
%% Files are named: t_vXX_aXX_dZ.dzn where 
%% t is the type of instance: c for complete, s for sparse
%% XX is the number of nodes
%% YY is the number of edges
%% Z is the diameter in required for that benchmark

int: diameter; % Diameter of the graph
bool: isDiameterOdd = (diameter mod 2 = 1);
int: nbV;     %Number of nodes                                      
int: nbE;     %Number of Edges
set of int: nodes = 1..nbV;
set of int: edges = 1..nbE;

array [edges,1..2] of nodes: en;       % For each edge, its endnodes.
array [nodes,edges] of bool: adj;      % For each node, wether an edge reaches that node or not.
array [edges,nodes] of bool: endnodes; % For each edge, whether a node is one of its endnodes. (Unused)
array [edges] of int: ws;              % Non-negative weight of each edge
int: radius;                           % Maximum radius (i.e. floor(D/2))

% DECISION VARIABLES: 
array [edges] of var bool: es;         %Which edges are part of the tree
var 0..sum(ws): objective;                            %Total weight of the tree
constraint objective = sum(i in edges)(bool2int(es[i])*ws[i]);

constraint sum(i in edges)(bool2int(es[i])) = nbV - 1;


% In order to get the diameter, choose a root for the tree and set the height of all other ndoes to 
% be less than the radius. 
%var nodes: root;
var 1..max(nbV, nbE): root;
array [nodes] of var 0..radius: h;     %Height of nodes
array [nodes] of var nodes: p;         %Parent of nodes

constraint 
    if isDiameterOdd then
        let {
            var nodes: a = en[root,1]; %root 1
            var nodes: b = en[root,2]; %root 2
        } in (
            root in edges
        /\  symmetry_breaking_constraint(a < b)
        /\  forall (e in edges) (en[e,1] == a /\ en[e,2] == b -> es[e] == true)
        /\  forall (e in edges) (en[e,1] == b /\ en[e,2] == a -> es[e] == true)
        /\  h[a] = 0 /\ h[b] = 0
        /\  p[a] = a /\ p[b] == b
        /\  forall (n in nodes where n != a /\ n != b) (h[n] > 0)
        /\  forall (i in nodes where i != a /\ i !=b ) (h[i] = h[p[i]] + 1)
            % Linking edge variables to height and parenthood.
        /\  forall (e in edges) (
                es[e] -> (
                    (h[en[e,1]] == h[en[e,2]] + 1 /\ p[en[e,1]] == en[e,2]) 
                \/  (h[en[e,2]] == h[en[e,1]] + 1 /\ p[en[e,2]] == en[e,1])
                ) 
            \/  (h[en[e,1]] == 0 /\ h[en[e,2]] == 0) % Case for the roots
            )
        )
    else
        root in nodes
    /\  h[root] = 0 /\ p[root] = root
    /\  forall (n in nodes where n != root) (h[n] > 0)
    /\  forall (i in nodes where i != root) (h[i] == h[p[i]] + 1)
        % Linking edge variables to height and parenthood.
    /\  forall (e in edges) (
            es[e] -> (
                (h[en[e,1]] == h[en[e,2]] + 1 /\ p[en[e,1]] == en[e,2]) 
            \/  (h[en[e,2]] == h[en[e,1]] + 1 /\ p[en[e,2]] == en[e,1])
            )
        )
    endif;


%Redundant constraints: Edge e1 doinated edge e2 in all the folloing situations.
constraint redundant_constraint(forall (e1, e2 in edges where ws[e1] < ws[e2] /\ en[e1,1] == en[e2,1]) (h[en[e1,2]] <= h[en[e2,2]] -> p[en[e1,1]] != en[e2,2]));
constraint redundant_constraint(forall (e1, e2 in edges where ws[e1] < ws[e2] /\ en[e1,2] == en[e2,2]) (h[en[e1,1]] <= h[en[e2,1]] -> p[en[e1,2]] != en[e2,1]));
constraint redundant_constraint(forall (e1, e2 in edges where ws[e1] < ws[e2] /\ en[e1,1] == en[e2,2]) (h[en[e1,2]] <= h[en[e2,1]] -> p[en[e1,1]] != en[e2,1]));

%Redundant constraints: Linking parenthood and edges.
constraint redundant_constraint(forall (e in edges) (p[en[e,1]] == en[e,2] -> es[e] == true));
constraint redundant_constraint(forall (e in edges) (p[en[e,2]] == en[e,1] -> es[e] == true));

%Good search strategy.
solve 
    :: seq_search([
        int_search([root]++h++p, input_order, indomain_min, complete),
        bool_search(es, input_order, indomain_min, complete)
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "root = ", show(root), ";\n",
    "h = ", show(h), ";\n",
    "p = ", show(p), ";\n",
    "es = ", show(es), ";\n",
    "objective = ", show(objective), ";\n"
];

%------------------------------------------------------------------------------%

