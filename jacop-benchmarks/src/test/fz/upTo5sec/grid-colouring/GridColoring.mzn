%------------------------------------------------------------------------------%
% new zinc file GridColoring.mzn
%------------------------------------------------------------------------------%
% Parameters

int: n;     % Width of grid
int: m;     % Height of grid

%------------------------------------------------------------------------------%
% Variables

array[1..n,1..m] of var 1..min(n,m): x; % Colour in each grid field
var 1..min(n,m): objective;             % Number of colours used

%------------------------------------------------------------------------------%
% Constraints

    % Constraining the objective
    %
constraint 
    forall(i in 1..n, k in 1..m)(x[i,k] <= objective);

    % Colouring rules
    %
constraint 
    forall(i in 1..n, j in i+1..n, k in 1..m, l in k+1..m)(
	    x[i,k] != x[i,l] \/ x[i,l] != x[j,l] 
    \/  x[j,k] != x[j,l] \/ x[i,k] != x[j,k]
    );
		 	
%------------------------------------------------------------------------------%
% Search and solve item

solve 
    :: seq_search([
        int_search([x[i,k] | i in 1..n, k in 1..m], first_fail, indomain_min, complete),
        int_search([objective], input_order, indomain_min, complete)
    ])
    minimize objective;		 	 

%------------------------------------------------------------------------------%
% Output item

output [
    "objective = \(objective);\n",
    "x = array2d(1..\(n), 1..\(m), \(x));\n"
] ++ [
    if k = 1 then "% " else "" endif ++
    "\(x[i,k])" ++ if k = m then "\n" else " " endif
| i in 1..n, k in 1..m
];

%------------------------------------------------------------------------------%
		 
