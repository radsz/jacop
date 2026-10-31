%------------------------------------------------------------------------------%
% Constrained Community Detection Problem
%
% The problem is to find communities in the graph with maximum modularity value 
% satisfying must-link and cannot-link constraints which indicate whether a 
% pair of vertices must assign to same or different communities.
%------------------------------------------------------------------------------%
% Includes

include "globals.mzn";
include "global_cardinality_low_up.mzn";
include "value_precede_chain.mzn";

%------------------------------------------------------------------------------%
% Input and Derived Parameters

int:n;
int:k;
int:maxsize;
%int:minsize;
int: nML;
int: nCL;
set of int: must = 1..nML;
set of int: cannot = 1..nCL;
array[must,1..2] of int: ML;
array[cannot,1..2] of int: CL;
array[1..n,1..n] of int: W;
array[1..n,1..n] of int: A;
array[1..n] of int: deg;
array[1..n] of set of 1..n: nbh =[ {j | j in 1..n where A[i,j] > 0} | i in 1..n];
int: dum = sum(i in 1..n)(W[i,i]);

%------------------------------------------------------------------------------%
% Variables

array[1..n] of var 1..k: x;
var 1..k: kk = max(x);

int: objub = 2*sum(i,j in 1..n where i < j)(W[i,j]) + dum;
var 0..objub: objective;

%------------------------------------------------------------------------------%
% Constraints

constraint value_precede_chain([i|i in 1..k], x);

constraint forall(m in must)( x[ML[m,1]] = x[ML[m,2]] );

constraint forall(c in cannot)( x[CL[c,1]] != x[CL[c,2]] );

constraint 
    global_cardinality_low_up(
        x, 
        [i | i in 1..k], 
        [0 | i in 1..k],
        [n | i in 1..k]
    );

    % Objective
    %
constraint
    objective = 2 * ( 
        sum(i in 1..n)(
            sum(j in 1..n where j < i)(
                bool2int(x[i] = x[j]) * W[i,j]
            )
        )
    ) + dum;

%------------------------------------------------------------------------------%
% Solve item and search

solve 
    :: int_search(x,input_order,indomain_min, complete) 
    maximize objective;

%------------------------------------------------------------------------------%
% Output

output [
    "x = \(x);\n",
%    "kk = \(kk);\n",
    "objective = \(objective);\n"
];

