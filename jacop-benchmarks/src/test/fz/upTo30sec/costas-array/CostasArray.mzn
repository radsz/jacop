%------------------------------------------------------------------------------%
% new zinc file CostasArray.mzn
% 
% The Costas Array problem: costas.mod
% 
% From http://mathworld.wolfram.com/CostasArray.html:
% An order-n Costas array is a permutation on {1,...,n} such
% that the distances in each row of the triangular difference
% table are distinct. For example, the permutation {1,3,4,2,5}
% has triangular difference table {2,1,-2,3}, {3,-1,1}, {1,2},
% and {4}. Since each row contains no duplications, the permutation
% is therefore a Costas array.
%
% Barry O'Sullivan -- b.osullivan@cs.ucc.ie
% Cork Constraint Computation Centre, Cork, Ireland
% September 2009
%------------------------------------------------------------------------------%

include "alldifferent.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n; % Size of Costas array

%------------------------------------------------------------------------------%
% Variables

array[1..n] of var 1..n: costas;
array[1..n,1..n] of var -n+1..n-1: differences;

%------------------------------------------------------------------------------%
% Constraints

constraint 
    alldifferent(costas);

% // How do the positions in the Costas array relate to the elements of the distance triangle.
% forall( ordered i,j in 1..n ) 
%    differences[<i,j>] = costas[j] - costas[j-i];

constraint 
    forall(i,j in 1..n)(
	    if i < j then
		    differences[i,j] = costas[j] - costas[j-i]
	    else    
            differences[i,j] = 0 
        endif % defensive modelling
	);
	

% // All entries in a particular row of the difference triangle must be distint.
% forall( i in 1..n-1 ) 
%    alldifferent( all (j in 1..n: j>i) differences[<i,j>] );
constraint 
    forall(i in 1..n-1)(
	    alldifferent(j in 1..n where i < j)(differences[i,j])
	);


% // All the following are redundant - only here to speed up search.

% // Symmetry Breaking
% costas[1] < costas[n];
constraint 
    symmetry_breaking_constraint(
        if 1 < n then costas[1] < costas[n] else true endif
    );


% // We can never place a 'token' in the same row as any other.
% forall (p in pairs) differences[p] <> 0;
constraint 
    redundant_constraint(
        forall(i,j in 1..n where i < j)(
	        differences[i,j] != 0
        )
	);


%forall ( ordered k,l in 3..n )
%    differences[<k-2,l-1>] + differences[<k,l>] = differences[<k-1,l-1>] + differences[<k-1,l>];
constraint 
    redundant_constraint(
        forall(k,l in 3..n where k < l)(
	        differences[k-2,l-1] + differences[k,l] = 
	        differences[k-1,l-1] + differences[k-1,l]
        )
    );

%------------------------------------------------------------------------------%
% Search and solve item

solve 
    :: int_search(costas, input_order, indomain_min, complete) 
    satisfy;

%------------------------------------------------------------------------------%
% Output item

output ["costas = ",show(costas),";\n"];

%------------------------------------------------------------------------------%

