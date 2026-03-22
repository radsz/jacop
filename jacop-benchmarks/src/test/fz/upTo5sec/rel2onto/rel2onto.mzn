%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Relational database to ontology.
% Matching:
%     -nbA: number of attributes to match.
%     -attribute_domains: possible matches for each attribute
%     -match_cost[a,b]: cost of matching a to value b.
%     -matching is bijective
%
% Treeness: 
%     -matches selected by the matching problem must appear
%         int the tree
%     -the tree must be connected accyclic
%     -therefore, higher nodes are used to connect the 
%     -matched nodes
%     -dnodes are the nodes that *can* get matched
%     -cnodes are nodes above, used to connect dnodes
%     -ws is the cost of each edge
%
% Objective:
%     -minimize the cost of the matching and the tree.
%
% To compile:
% mzn2fzn model.mzn alignment.dzn X.integration.dzn
% alignment.dzn contains data for the tree part 
% X.integration.dzn constains data for the Xth instance of
%    the matching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%-----------------------------------------------------------------------------%
% Includes

include "alldifferent.mzn";
include "arg_sort.mzn";

%-----------------------------------------------------------------------------%
% Parameters

    % Graph parameters
    %
int: nbV;
int: nbE;
set of int: nodes = 1..nbV;
set of int: edges = 1..nbE;
set of int: cnodes;
set of int: dnodes;
set of int: anodes;  %Is always empty on these data files.
array[nodes,edges] of bool: adjacent;
array[edges] of nodes: heads;
array[edges] of nodes: tails;
array[1..2,edges] of int: endpairs = array2d(1..2,edges,tails++heads);
array[edges] of int: ws;
array[edges] of int: sorted_edges = arg_sort(ws);

% Bounds for the edge cost variable
int: w_lb = sum(e in edges)(min(0, ws[e]));
int: w_ub = sum(e in edges)(max(0, ws[e]));

    % Attribute parameters
    %
int: nbA;
set of int: atts = 1..nbA;
array[atts] of set of int: attribute_domains;  
array[atts] of int: attribute_names; % just for printing

array[atts,int] of int: match_costs;
array[atts,int] of int: match_costs_sorted; 

% Bounds for the matching variables
int: match_lb = min([min(attribute_domains[a]) | a in atts]);
int: match_ub = max([max(attribute_domains[a]) | a in atts]);

% Bounds for the matching cost variable
int: wm_lb = sum(a in atts)(min(i in attribute_domains[a])(match_costs[a,i]));
int: wm_ub = sum(a in atts)(max(i in attribute_domains[a])(match_costs[a,i]));

%-----------------------------------------------------------------------------%
% Variables

array[nodes] of var bool: vs;
array[edges] of var bool: es;
array[atts] of var match_lb..match_ub: match;
var w_lb..w_ub: w;
var wm_lb..wm_ub: wm;
var w_lb+wm_lb..w_ub+wm_ub: objective;

%-----------------------------------------------------------------------------%
% Functions

function int: other(array[1..2,int] of int: endpairs, int: snd, int: r) =
	if endpairs[1,snd] == r then endpairs[2,snd] else endpairs[1,snd] endif;

%-----------------------------------------------------------------------------%
% Predicates

predicate treep(
    array[int] of var bool: vs, array[int] of var bool: es,
    array [int,int] of bool: adjacent, array[1..2,int] of int: endpairs
) = 
	forall(e in index_set(es))(
        es[e] -> (vs[endpairs[1,e]] /\ vs[endpairs[2,e]])
    ) 
/\  let {
		% Parent node:
		array[index_set(vs)] of var index_set(vs): p;
		% A variable root for the tree
		var index_set(vs): root ;
		% Adjacency matrix: node->node->edge
		array[index_set(vs),index_set(vs)] of int: m = 
	        array2d(index_set(vs),index_set(vs),
                [ sum(
                    % the intersect will contain only one element or 0 elements.
                    (   { e| e in index_set(es) where adjacent[i,e]} 
                        intersect { e| e in index_set(es) where adjacent[j,e]}
                    ) union {0}
                  ) 
                | i,j in index_set(vs)]
            ); 
    } in 
	    vs[root] 
    /\  p[root] = root
	    % Parent must be adjacent
    /\  forall(a in index_set(vs) where a != root /\ vs[a])(
            p[a] in {other(endpairs,b,a) | b in index_set(es) where adjacent[a,b]}
        ) 
	    % Edge between child and parent, force parent in, avoid cyclic 
        % relationships
    /\  forall(a in index_set(vs) where a != root /\ vs[a])(
            es[m[a,p[a]]] /\ vs[p[a]] /\ p[p[a]] != a
        ) 
	    % Set out-nodes to a value.
    /\  forall(a in index_set(vs) where not(vs[a]))(
            p[a] = a
        )
	    % Redundant:
    /\  redundant_constraint(
            sum(i in index_set(es))(bool2int(es[i])) 
                = sum(i in index_set(vs))(bool2int(vs[i])) - 1
        )
    ;

%-----------------------------------------------------------------------------%
% Constraints

% Attrbiutes are in the tree (empty constraint for these data files)
constraint forall(att in anodes)( vs[att] == true );

% Enforce the treeness
constraint treep(vs,es,adjacent,endpairs);

% Matching problem:
constraint forall(a in atts)( match[a] in attribute_domains[a] );
constraint forall(a in atts)( vs[match[a]] );
constraint alldifferent(match);

% Matched node is in the tree.
constraint forall(d in dnodes)( exists(a in atts)(match[a] == d) <-> vs[d] );
% Onlly one edge comming out of the match.
constraint forall(d in dnodes)( vs[d] <-> sum(e in edges where adjacent[d,e])(es[e]) == 1 );

% Objective related constraints
constraint w = sum(i in edges)( bool2int(es[i]) * ws[i] ); % Weight of the tree
constraint wm = sum(a in atts)( match_costs[a, match[a]] );
constraint objective = w + wm;


%-----------------------------------------------------------------------------%
% Search strategies


ann: cheap_matches = int_search(
    [ match[a] == match_costs_sorted[a,i] |a in atts, i in index_set_2of2(match_costs_sorted) ], 
    input_order, indomain_max, complete
);

ann: naive_e  = int_search(es, input_order, indomain_min, complete);
ann: kruskal  = int_search([es[sorted_edges[e]] | e in edges], input_order, indomain_max, complete);
ann: kruskal2 = int_search([es[sorted_edges[nbE + 1 - e]] | e in edges], input_order, indomain_min, complete);


solve 
    ::seq_search([
        %cheap_matches, 
        int_search(match, first_fail, indomain_min, complete),
        kruskal2,
    ])
    minimize objective;

output [
    "es = \(es);\n",
    "vs = \(vs);\n",
    "match = \(match);\n",
    "objective = \(objective);\n"
];

%output ["digraph {\n"]++
%[ "  \(n-1)"++ (if n in cnodes then "[fillcolor=\"#59d0a0\",style=filled];" else if n in dnodes then "[fillcolor=gold,style=filled];" else "" endif endif)++"\n" | n in nodes  where fix(vs[n])] ++ 
%[ "  "++if fix(heads[e]) in cnodes then "\(heads[e]-1) -> \(tails[e]-1)" else "\(tails[e]-1) -> \(heads[e]-1)" endif ++" [label=\"w=\(ws[e]/10000)\"];\n" | e in edges  where fix(es[e])] ++ 
%[ "  \(attribute_names[a]) [shape=hexagon];\n" | a in atts] ++
%[ "  \(match[a]-1) -> \(attribute_names[a]) [label=\"w=\(match_costs[a,fix(match[a])]/10000)\"];\n" | a in atts]++
%["}\nobjective = \(objective)\nwm = \(wm)\nw =\(w)"];

