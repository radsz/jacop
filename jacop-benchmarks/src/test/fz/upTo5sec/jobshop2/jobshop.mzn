% Jobshop model created by Krzysztof Kuchcinski
%
% More instances in the same data format can be found at
% http://people.brunel.ac.uk/~mastjjb/jeb/orlib/files/jobshop1.txt

include "globals.mzn";

int: n;
int: m;
int: span=2000;

array [1..n, 1..2*m] of int: job;
array [1..n, 1..m] of var 0..span: t;
array [1..n] of int: one = [ 1 | i in 1..n];

% Was called end, changed to conform to challenge rules.
%
var 0..span: objective;

constraint
	forall(i in 1..n, j in 1..m-1) ( t[i,j] + job[i, 2*j] <= t[i, j+1] );

constraint
	forall(k in 1..m) (
	   let {
	      array[1..n] of int: d = [ job[i, 2*j] | i in 1..n, j in 1..m where job[i,2*j-1] = k-1],
	      array[1..n] of var 0..span: s = [ t[i,j] | i in 1..n, j in 1..m where job[i,2*j-1] = k-1]
	   }
	   in
	   cumulative(s, d, one, 1)
	   );

constraint 
	maximum(objective, [ t[i, m] + job[i, 2*m] | i in 1..n]);

solve ::
      int_search([t[i,j] | i in 1..n, j in 1..m], smallest, indomain_min, complete)
      minimize objective;

output [
   "t = ", show(t), "\n",
   "objective = ", show(objective), "\n"
];
