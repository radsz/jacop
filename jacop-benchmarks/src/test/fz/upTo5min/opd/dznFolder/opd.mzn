%------------------------------------------------------------------------------%
% Important NOTE
%
% Requires MiniZinc >= 2.0.2 for the symmetry_breaking_constraint predicate
%
%------------------------------------------------------------------------------%
%% Design of Collateralised Debt Obligations Squared (CDO^2) Transactions
%%
%% Problem described in:
%%   Pierre Flener, Justin Pearson, Luis G. Reyna, Olof Sivertsson:
%%   Design of Financial CDO Squared Transactions Using Constraint Programming.
%%   Constraints 12(2):179-205, 2007
%%   http://dx.doi.org/10.1007/s10601-006-9014-4
%%   
%% Also solved with:
%%   LS with VNS: http://dx.doi.org/10.1016/j.endm.2014.11.017
%%   CBLS with set variables: http://dx.doi.org/10.1007/11564751_7
%%
%% Authors: Pierre Flener and Jean-Noel Monette
%%
%% Model loosely based on Ralph Becket's BIBD model at
%%   https://github.com/MiniZinc/minizinc-benchmarks/blob/master/bibd/bibd.mzn
%%
%------------------------------------------------------------------------------%
% An OPD (v, b, r) problem is to find a binary matrix of v rows
% and b columns such that each row sums to r, and
% the dot product beween any pair of distinct rows is minimal.
%
%------------------------------------------------------------------------------%
% Includes

include "lex_greatereq.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: v;                     % Number of rows
int: b;                     % Number of columns
int: r;                     % Row sum

set of int: rows = 1..v;    % Set of rows
set of int: cols = 1..b;    % Set of columns

%------------------------------------------------------------------------------%
% Lower bound computation for lambda

int: rv = r*v;
int: rvmodb = rv mod b;
int: floorrv = rv div b;
int: ceilrv = rv div b + bool2int(rv mod b != 0);
int: num = (ceilrv*ceilrv*rvmodb+floorrv*floorrv*(b-rvmodb)-rv);
int: denom = v*(v-1);
int: lb_lambda = num div denom + bool2int( num mod denom !=0);

%------------------------------------------------------------------------------%
% This line is there for debugging purposes, it can be safely removed

%int: tmp = trace("% Computed lower bound for lambda: "++show(lb_lambda)++"\n",lb_lambda);

%------------------------------------------------------------------------------%
% Variables

array [rows, cols] of var 0..1: m;  
var lb_lambda..b: objective;        % The 'lambda' variable

%------------------------------------------------------------------------------%
% Constraints

    % Every row must sum to r.
    %
constraint forall (i in rows) (sum (j in cols) (m[i, j]) = r);

    % The dot product of every pair of distinct rows must be at most lambda for 
    % an OPD and a PD, and equal to lambda for a BIBD
constraint forall (i_a, i_b in rows where i_a < i_b) (
    sum (j in cols) (m[i_a, j] * m[i_b, j]) <= objective
);

    % Break row symmetry in the incidence matrix.
    %
constraint symmetry_breaking_constraint(
    forall(i in rows diff {max(rows)})(
        lex_greatereq([m[i, j] | j in cols], [m[i+1, j] | j in cols])
    )
);

    % Break column symmetry in the incidence matrix.
    %
constraint symmetry_breaking_constraint(
    forall(j in cols diff {max(cols)})(
        lex_greatereq([m[i, j] | i in rows], [m[i, j+1] | i in rows])
    )
);

%------------------------------------------------------------------------------%
% Search and solve item

solve 
    :: seq_search([
            int_search([m[i, j] | i in rows, j in cols], input_order, indomain_max, complete),
       		int_search([objective], input_order, indomain_min, complete)
    ])
    minimize objective; 

%------------------------------------------------------------------------------%
% Output itme

output [
    "% lb(lambda) = ", show(lb_lambda), ";\n",
    "objective = ", show(objective), ";\n",
    "m = array2d(", show(rows), ", ", show(cols), ", ", show(m), ");\n"
];
% Disabled the full solution. Printing only the objective value, lower bound, and parameters.
%output  ["opd: (v = ", show(v), ", b = ", show(b), ", r = ", show(r), "). Found lambda = ", show(objective),"\tlb: ", show(lb_lambda)]
%       ++["\n\n"] ++ 
%	[ ( if j > b then "\n" else 
%	        if fix(m[i,j])=1 then "*" else " " endif
%	    endif )
%       | i in rows, j in 1..(b + 1) ]
%;
%------------------------------------------------------------------------------%

