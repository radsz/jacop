include "cumulative.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: m; % number of minerals
array[1..m] of int: f; % flow rate;

int: r; % number of recipes
array[1..r,1..m] of int: c; % c[k,i] use of mineral i in recipe k

int: n; % number of orders
array[1..n] of 1..r: t;	% recipe of order
array[1..n] of int : h; % height
array[1..n] of int : w; % width

int: nl; % number of lines;

int: p; % number of production rules
array[1..p] of 1..4: typ; % type of rule
array[1..p] of 1..r: k1;
array[1..p] of int : d;
array[1..p] of 1..r: k2;

array[1..r] of int: duration = 
	    [ sum(i in 1..n)(bool2int(t[i] == j)*h[i]*w[i]) | j in 1..r ];

int: horiz = 1000; % sum(i in 1..n)(h[i]*w[i]);

%------------------------------------------------------------------------------%
% Variables

array[1..n] of var 0..horiz: s;
array[1..n] of var 0..horiz: e = [ s[i] + h[i]*w[i] | i in  1..n];
array[1..n] of var 1..nl: l; 
var 0..horiz: makespan;

array[1..r] of var 0..horiz: start;
array[1..r] of var 0..horiz: end = [ start[i] + duration[i] | i in 1..r ];
array[1..r] of var 1..nl: line;

array[1..p] of var bool: followed;

var 0..p: violation = sum(i in 1..p)(1 - bool2int(followed[i]));
var 0..1000*p+horiz: objective = 1000 * violation + makespan;

%------------------------------------------------------------------------------%
% Constraints

% set start times of individual products as offset from recipe
constraint 
	forall(i in 1..n)(
		s[i] = start[t[i]] 
				+ sum(j in 1..i-1)(bool2int(t[i] == t[j]) * h[j] * w[j]) 
	/\	l[i] = line[t[i]]
	);

%% redundant lines constraint
constraint cumulative(start, duration, [1| i in 1..r], nl);

%% Each line only has one product at a time 
constraint forall(i in 1..nl)(
	cumulative(start, duration, [bool2int(line[j] == i) | j in 1..r], 1)
);

%% flow constraints;
constraint forall(i in 1..m)(
	cumulative(start, duration, [c[k,i] | k in 1..r], f[i])
);

% production rules
constraint forall(i in 1..p)(
	if typ[i] == 1 then
	   followed[i] -> end[k1[i]] + d[i] <= start[k2[i]]
	else if typ[i] == 2 then
	   followed[i] -> end[k1[i]] + d[i] >= start[k2[i]]
	else if typ[i] == 3 then
	   followed[i] -> start[k1[i]] <= start[k2[i]] + d[i]
	else if typ[i] == 4 then
	   followed[i] -> end[k1[i]] <= end[k2[i]] + d[i]
	else true endif endif endif endif
);

%% makespan
constraint forall(i in 1..r)(makespan >= end[i]);

%------------------------------------------------------------------------------%
% Search

solve 
	:: seq_search([
		int_search( start    , smallest   , indomain_min, complete),
		int_search( line     , input_order, indomain_min, complete),
		bool_search(followed , input_order, indomain_min, complete),
		int_search([makespan], input_order, indomain_min, complete)
	])
   	minimize objective;

%------------------------------------------------------------------------------%
% Output

output [
	"s = ", show(s), ";\n",
	"%% e = ", show(e), ";\n",
	"l = ", show(l), ";\n",
    "constraint objective = ", show(objective), ";\n"
];







