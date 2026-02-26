%------------------------------------------------------------------------%
% Find a perfect 1-factorization of the graph K_n
%------------------------------------------------------------------------%
%
% A 1-factorization is a partition of the edges of the graph into m-1
% complete matchings. For the 1-factorization to be perfect, every
% pair of matchings must form a Hamiltonian circuit of the graph. To
% make the problem interesting it is specified as an
% optimization-problem, forcing an ordering on the solutions.
%
% This model tests using several different global constraints in the 
% same model. The global constraints used are:
%  - alldifferent
%  - inverse
%  - lex_less
%  - element
% Unfortunately, a decomposition of circuit is used since it is not
% available in the MiniZinc distribution. 
%
% In particular, the proof of optimality takes a very long time if
% strong pruning for alldifferent is not used.
%
%  Main authors:
%     Mikael Zayenz Lagerkvist <lagerkvist@gecode.org>
%
%  Copyright:
%     Mikael Zayenz Lagerkvist, 2009
%
%  Permission is hereby granted, free of charge, to any person obtaining
%  a copy of this software and associated documentation files (the
%  "Software"), to deal in the Software without restriction, including
%  without limitation the rights to use, copy, modify, merge, publish,
%  distribute, sublicense, and/or sell copies of the Software, and to
%  permit persons to whom the Software is furnished to do so, subject to
%  the following conditions:
%
%  The above copyright notice and this permission notice shall be
%  included in all copies or substantial portions of the Software.
%
%  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
%  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
%  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
%  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
%  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
%  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
%  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
%
%------------------------------------------------------------------------%

include "globals.mzn";

%------------------------------------------------------------------------%
% Predicates
%------------------------------------------------------------------------%

%
% Two arrays form a hamiltonian circuit in c
%
predicate union_circuit( array[int] of var int: x,
	  		 array[int] of var int: y) =
	  		 %array[int] of var int: c) =
	let { int: n = length(x),
	      array[1..n] of var 1..n: c
	} in
	  %% The successor in c is either the successor in x or in y
	  forall(i in 1..n) (
	  let {
		var 1..2: index
	  } in
		[x[i], y[i]][index] = c[i]
	  ) /\
	  %% Must be hamiltonian curcuit
	  circuit(c) /\
	  %% Symmetry breaking
	  symmetry_breaking_constraint(c[1] == x[1])
;


%------------------------------------------------------------------------%
% Parameters
%------------------------------------------------------------------------%

% Nodes in graph
int: n;
% Number of matchings
int: m = n-1;

% Data
%n = 11;


%------------------------------------------------------------------------%
% Variables
%------------------------------------------------------------------------%

% Each row represents a matching
array[1..m, 1..n] of var 1..n: p;

% Objective for ordering of solutions
int: obj_lb = sum(i in 1..n)(i);
int: obj_ub = sum(i in 1..n)(i * n);
var obj_lb..obj_ub: objective = sum(i in 1..n) (i * p[1, i]);

%------------------------------------------------------------------------%
% Constraints
%------------------------------------------------------------------------%

% No self-loops
constraint
	forall(row in 1..m) (
		   forall(col in 1..n) (
		   	      p[row, col] != col
		   )
	);

% Each row is a matching
constraint
	forall(row in 1..m) (
	let {
		% The row
		array[1..n] of var int: ra = [p[row, i] | i in 1..n]
	} in
		inverse(ra, ra) :: domain
	);

% The rows form a partition
% This is ensured by letting all columns be all different.
constraint
	forall(col in 1..n) (
	let {
		% The column
		array[1..m] of var int: c = [p[i, col] | i in 1..m]
	} in
		alldifferent(c) :: domain
	);

% Each pair of rows gives a hamiltonian circuit
constraint
	forall(rowa,rowb in 1..m where rowa<rowb) (
	let {
		array[1..n] of var int: ra = [p[rowa, i] | i in 1..n],
		array[1..n] of var int: rb = [p[rowb, i] | i in 1..n]
	} in
		union_circuit(ra, rb) :: domain
	);

% Symmetry breaking for order of factors
constraint
	forall(row in 1..m-1) (
        symmetry_breaking_constraint(
	        let {
	        	array[1..n] of var int: ra = [p[row  , i] | i in 1..n],
	        	array[1..n] of var int: rb = [p[row+1, i] | i in 1..n]
	        } in
	        	lex_less(ra, rb)
        )
	);

%------------------------------------------------------------------------%
% Search
%------------------------------------------------------------------------%

solve 
    :: int_search(
            [p[i,j] | i in 1..m, j in 1..n], 
            input_order, indomain_min, complete
    ) 
    minimize objective;

output [
    "p = \(p);\n",
    "objective = \(objective);\n"
];

