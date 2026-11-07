%------------------------------------------------------------------------------%
% Multi Dimensional Knapsack Problem
%------------------------------------------------------------------------------%

include "knapsack.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: N; % number of variables
int: M; % number of constraints

set of int: VRange = 1..N;
set of int: CRange = 1..M;

array[CRange,VRange] of int: a;     % Weight of items per bin
array[CRange] of int: b;            % Sizes of bins
array[VRange] of int: c;            % Profit of items

%------------------------------------------------------------------------------%
% Ignored parameters

int: z;                             % Normally the optimal value

%------------------------------------------------------------------------------%
% Variables

array[VRange] of var 0..1: x;               % Whether an item is packed
array[CRange] of var 0..ub_array(b): bVar;  % Total weight in a bin

var 0..sum(c): objective = sum(i in VRange)(c[i] * x[i]);   % Total profit

%------------------------------------------------------------------------------%
% Constraints

    % Constraining the size of the bins
    %
constraint
	forall(i in CRange)( bVar[i] >= 0 /\ bVar[i] <= b[i] );

    % Knapsack constraints
    %
constraint
	forall(i in CRange)( 
        knapsack([a[i,j] | j in VRange], c, x, bVar[i], z) 
    );  

%------------------------------------------------------------------------------%
% Some integrety check for the (input) data

constraint 
    forall(i in CRange,j in VRange)(
        assert(a[i,j] >= 0, "negative values in a") 
    );
constraint 
    forall(i in CRange)( assert(b[i] >= 0, "negative values in b") );
constraint 
    forall(j in VRange)( assert(c[j] >= 0, "negative values in c") );
constraint assert(z >= 0, "negative z");

%------------------------------------------------------------------------------%
% Search

solve 
    :: int_search(x, input_order, indomain_max, complete)
    maximize objective;

%------------------------------------------------------------------------------%
% Output

output [ 
    "x = ", show(x), ";\n",
    "objective = ", show(objective), ";\n"
];

%------------------------------------------------------------------------------%
