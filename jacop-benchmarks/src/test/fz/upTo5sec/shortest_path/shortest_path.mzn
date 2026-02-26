%------------------------------------------------------------------------------%
% Jakob Puchinger <jakobp@cs.mu.oz.au>
% June 2008
% vim: ft=zinc ts=4 sw=4 et tw=0
%
% Shortest Path Problem.
% 
%------------------------------------------------------------------------------%

    % Number of nodes
int: N;
    % Start node
1..N: Start;
    % End node
1..N: End;
    % Number of edges (directed arcs)
int: M;
    %  The actual edges
set of int: Edges = 1..M;
    % Edge lengths
array[Edges] of int: L;
    % Edge start node
array[Edges] of 1..N: Edge_Start;
array[Edges] of 1..N: Edge_End;

    % Variable indicating if edge is used
array[Edges] of var 0..1: x;

constraint
    forall( i in 1..N ) (
        if i = Start then
                % outgoing flow
            sum(e in Edges where Edge_Start[e] = i)(x[e]) - 
                % incoming flow
            sum(e in Edges where Edge_End[e] = i)(x[e])
            = 1
        elseif i = End then
            sum(e in Edges where Edge_Start[e] = i)(x[e]) - 
            sum(e in Edges where Edge_End[e] = i)(x[e])
            = -1
        else
            sum(e in Edges where Edge_Start[e] = i)(x[e]) - 
            sum(e in Edges where Edge_End[e] = i)(x[e])
            = 0
        endif
    );


solve minimize sum(e in Edges)( L[e] * x[e] );

output ["Length: ", show(sum(e in Edges)(L[e] * x[e])), "\n"] ++
       ["Start : ", show(Start), "\n"] ++
       ["End   : ", show(End), "\n\n"] ++
       ["Edges in shortest path:\n"] ++
       [ if   fix(x[e]) = 1
         then show(Edge_Start[e]) ++ " -> " ++ show(Edge_End[e]) ++ "\n" 
         else "" 
         endif | e in Edges
       ];

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
